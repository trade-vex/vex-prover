use crate::{
    executor::{flatten_single, instruction::IMTOperation},
    imt::{
        leaf::Leaf,
        side::{Buy, Sell},
    },
};
use std::{array, marker::PhantomData};

use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::{
    components::{
        less_than::{LessThanElements, StrictLessThanElements},
        poseidon::PoseidonElements,
        Claim,
    },
    executor::instruction::{Instruction, InstructionElements},
    flatten,
    hash::{N_HASH, N_STATE},
    imt::{
        leaf::LeafColumn,
        side::{OrderSide, Side},
        IndexBits, LeafFelts, MerklePath, MerkleProof, MERKLE_HEIGHT, N_LEAF_FELTS, N_U64_FELTS,
    },
};

use super::InsertionsColumn;

#[derive(Clone)]
pub struct InsertionsEval<S> {
    pub claim: Claim<InsertionsColumn>,
    pub poseidon_elements: PoseidonElements,
    pub less_than_elements: LessThanElements,
    pub strict_less_than_elements: StrictLessThanElements,
    pub instruction_elements: InstructionElements,
    pub _side: PhantomData<S>,
}

/// This implementation of the `FrameworkEval` trait for `InsertionsEval` provides methods to evaluate
/// constraints on Insertions to Buy and Sell IMT;
///
/// # Constaint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///  Insertion Operation happens in two steps
///  1) Updating the low leafs's "next" value
///  2) Updating the inactive leaf's value
///  The constraints must ensure that the low leaf is indeed the "low" leaf of the order being inserted.
///  The constraints must ensure that the updates are done correctly.
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. Assert that the opcode is equal to the Insertion opcode.
///   4. Assert that the inserted leaf's time is strictly greater than the low leaf's time and low leaf's next time.
///      - [low_time, inserted_time, 1] must be in the strict_less_than_elements relation.
///      - [next_time, inserted_time, 1] must be in the strict_less_than_elements relation.
///   5. Assert that the prices are checked according to the side of the order.
///      - Buy: => general priority is low_price >= inserted_price > next_price
///          - [inserted_price, low_price, 1] must be in the less_than_elements relation.
///          - [next_price, inserted_price, 1] must be in the strict_less_than_elements relation.
///      - Sell: => general priority is low_price <= inserted_price < next_price
///          - [low_price, inserted_price, 1] must be in the less_than_elements relation.
///          - [inserted_price, next_price, 1] must be in the strict_less_than_elements relation.
///   6. Assert that the initial root hash of the initial state is equal to the root hash in the merkle path of the low leaf.
///   7. Assert that low leaf's next value is equal to the inserted leaf's next value before the insertion.
///   8. The Low leaf is part of the Merkle Tree by verifying the Merkle Proof.
///      - The Merkle Proof is a list of sibling hashes from the leaf to the root.
///      - The Merkle Path is a list of hashes from the leaf to the root.
///      - IndexBits is the binary representation of the index of the leaf.
///   9. Update the Low Leaf's next value by replacing the "next" value with the "label" of the leaf being inserted
///   10. Ensure that the resultant root hash from updating the low leaf is equal to the root contained in inactive leaf's merkle path.
///   11. Verify the Merkle Proof of the Inactive Leaf.
///   12. Update the Inactive Leaf's value to the inserted leaf using the updated_merkle_path.
///   13. Ensure that the final state's count is equal to the initial state's count plus 1.
///   14. Verify that the final root hash of the final state is equal to the root hash in the merkle path of the updated leaf.
///   15. The Priority must be updated only if the low leaf is the first leaf in the tree.
///       - The priority of the leaf will change only if the low leaf is the first leaf in the tree.
///           (verifying the priority i.e label of the leaf to the state.priority)
///       - the updated priority must be equal to the inserted leaf's (price, time) pair.
///   16. Yield the Results by adding the values to the ProcessorLookupElements.   
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///   17. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
impl<S: OrderSide> FrameworkEval for InsertionsEval<S> {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let op = Instruction::<E::F>::from_eval(&mut eval);

        // is_real must be a boolean
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));

        // opcode must be equal to the instruction's opcode
        eval.add_constraint(op.opcode.clone() - E::F::from(S::op_code(IMTOperation::Insertion)));

        let mult = E::EF::from(op.is_real.clone());

        // low_leaf must be active
        eval.add_constraint(E::F::one() - op.low_leaf[0].clone());

        let low_price: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.low_leaf[LeafColumn::PRICE + i].clone());
        let low_time: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.low_leaf[LeafColumn::TIME + i].clone());
        let inserted_price: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.leaf[LeafColumn::PRICE + i].clone());
        let inserted_time: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.leaf[LeafColumn::TIME + i].clone());
        let next_price: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.low_leaf[LeafColumn::NEXT_PRICE + i].clone());
        let next_time: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.low_leaf[LeafColumn::NEXT_TIME + i].clone());
        // time of inserted leaf must be greater than time of low leaf and low leaf's next
        eval.add_to_relation(RelationEntry::new(
            &self.strict_less_than_elements,
            mult.clone(),
            &chain!(
                low_time.iter().cloned(),
                inserted_time.iter().cloned(),
                [E::F::one()]
            )
            .collect_vec(),
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.strict_less_than_elements,
            mult.clone(),
            &chain!(
                next_time.iter().cloned(),
                inserted_time.iter().cloned(),
                [E::F::one()]
            )
            .collect_vec(),
        ));
        match S::side() {
            Side::Buy => {
                // price of inserted leaf must be less than price of low leaf price.
                eval.add_to_relation(RelationEntry::new(
                    &self.less_than_elements,
                    mult.clone(),
                    &chain!(
                        inserted_price.iter().cloned(),
                        low_price.iter().cloned(),
                        [E::F::one()]
                    )
                    .collect_vec(),
                ));
                // price of next must be stritly less than price of inserted leaf
                eval.add_to_relation(RelationEntry::new(
                    &self.strict_less_than_elements,
                    mult.clone(),
                    &chain!(
                        next_price.iter().cloned(),
                        inserted_price.iter().cloned(),
                        [E::F::one()]
                    )
                    .collect_vec(),
                ));

                // initial state's buy root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.buy_root_hash[i].clone()
                            - op.low_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
            }
            Side::Sell => {
                // price of low leaf must less than price of inserted leaf
                eval.add_to_relation(RelationEntry::new(
                    &self.less_than_elements,
                    mult.clone(),
                    &chain!(
                        low_price.iter().cloned(),
                        inserted_price.iter().cloned(),
                        [E::F::one()]
                    )
                    .collect_vec(),
                ));

                // price of inserted leaf must be strictly less than price of next
                eval.add_to_relation(RelationEntry::new(
                    &self.strict_less_than_elements,
                    mult.clone(),
                    &chain!(
                        inserted_price.iter().cloned(),
                        next_price.iter().cloned(),
                        [E::F::one()]
                    )
                    .collect_vec(),
                ));

                // initial state's sell root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.sell_root_hash[i].clone()
                            - op.low_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
            }
        }

        // the low leafs next value must be equal to the inserted leaf's next before the insertion
        for i in 0..2 * N_U64_FELTS {
            eval.add_constraint(
                op.low_leaf[LeafColumn::NEXT + i].clone() - op.leaf[LeafColumn::NEXT + i].clone(),
            );
        }

        // eval low leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.low_merkle_path.clone(),
            op.low_leaf.clone(),
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );
        let mut updated_low_leaf = op.low_leaf.clone();
        updated_low_leaf[LeafColumn::NEXT..].clone_from_slice(&op.leaf[9..25]);
        // eval updated low leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.updated_low_merkle_path.clone(),
            updated_low_leaf,
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // the resultant root hash from updating low_leaf must be equal the path of inactive leaf
        // this ensures that both leaf updates are consistent
        for i in 0..N_HASH {
            eval.add_constraint(
                op.updated_low_merkle_path[MERKLE_HEIGHT][i].clone()
                    - op.merkle_path[MERKLE_HEIGHT][i].clone(),
            );
        }

        let inactive_leaf: [E::F; N_LEAF_FELTS] = array::from_fn(|_| E::F::zero());

        // eval empty leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.merkle_path.clone(),
            inactive_leaf,
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );
        // eval updated leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.updated_merkle_path.clone(),
            op.leaf.clone(),
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // ensure that the state count is updated correctly
        eval.add_constraint(op.final_state.n.clone() - op.initial_state.n.clone() - E::F::one());
        match S::side() {
            Side::Buy => {
                // final state's buy root hash must be equal to the root in the inserted leaf's merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.buy_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the initial priority for sell IMT must be equal to the final priority
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.sell_imt_priority[i].clone()
                            - op.final_state.sell_imt_priority[i].clone(),
                    );
                }

                // the initial priority for buy IMT must change only if the low leaf is the first leaf in the buy imt
                // if the priority of the leaf changes, it must be equal to the inserted leaf's price_time
                let first_leaf_price_time = Leaf::<E::F, Buy>::first_price_time_felts();
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        (op.final_state.buy_imt_priority[i].clone()
                            - op.initial_state.buy_imt_priority[i].clone())
                            * (op.low_leaf[LeafColumn::PRICE + i].clone()
                                - first_leaf_price_time[i].clone()),
                    );

                    eval.add_constraint(
                        (op.final_state.buy_imt_priority[i].clone()
                            - op.initial_state.buy_imt_priority[i].clone())
                            * (op.final_state.buy_imt_priority[i].clone()
                                - op.leaf[LeafColumn::PRICE + i].clone()),
                    );
                }
            }
            Side::Sell => {
                // final state's sell root hash must be equal to the root in the inserted leaf's merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.sell_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the initial priority for buy IMT must be equal to the final priority
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.buy_imt_priority[i].clone()
                            - op.final_state.buy_imt_priority[i].clone(),
                    );
                }

                // the initial priority for sell IMT must change only if the low leaf is the first leaf in the sell IMT
                // if the priority of the leaf changes, it must be equal to the inserted leaf's price_time
                let first_leaf_price_time = Leaf::<E::F, Sell>::first_price_time_felts();
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        (op.final_state.sell_imt_priority[i].clone()
                            - op.initial_state.sell_imt_priority[i].clone())
                            * (op.low_leaf[LeafColumn::PRICE + i].clone()
                                - first_leaf_price_time[i].clone()),
                    );

                    eval.add_constraint(
                        (op.final_state.sell_imt_priority[i].clone()
                            - op.initial_state.sell_imt_priority[i].clone())
                            * (op.final_state.sell_imt_priority[i].clone()
                                - op.leaf[LeafColumn::PRICE + i].clone()),
                    );
                }
            }
        }

        let values: Vec<E::F> = flatten!(
            op.initial_state.n,
            op.initial_state.buy_root_hash,
            op.initial_state.buy_imt_priority,
            op.initial_state.sell_root_hash,
            op.initial_state.sell_imt_priority,
            op.opcode,
            op.low_merkle_proof,
            op.low_merkle_path,
            op.updated_low_merkle_path,
            op.low_index,
            op.low_leaf,
            op.merkle_proof,
            op.merkle_path,
            op.updated_merkle_path,
            op.index,
            op.leaf,
            op.final_state.n,
            op.final_state.buy_root_hash,
            op.final_state.buy_imt_priority,
            op.final_state.sell_root_hash,
            op.final_state.sell_imt_priority,
            op.is_real
        );
        // yield the results
        eval.add_to_relation(RelationEntry::new(
            &self.instruction_elements,
            -mult,
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

fn eval_merkle_proof<E: EvalAtRow>(
    eval: &mut E,
    proof: MerkleProof<E::F>,
    path: MerklePath<E::F>,
    leaf: LeafFelts<E::F>,
    index_bits: IndexBits<E::F>,
    poseidon_elements: &PoseidonElements,
    mult: E::EF,
) {
    // evaluate leaf hash
    let leaf: Vec<E::F> = leaf[0..N_STATE].into();
    eval.add_to_relation(RelationEntry::new(
        poseidon_elements,
        mult.clone(),
        &chain!(leaf.iter().cloned(), path[0].clone().into_iter()).collect::<Vec<_>>(),
    ));

    let mut curr = path[0].clone();
    for (i, (sibling, hash)) in proof.iter().zip(path.iter().skip(1)).enumerate() {
        let index_bit = index_bits[i].clone();
        let first: [E::F; N_HASH] = array::from_fn(|j| {
            index_bit.clone() * sibling[j].clone()
                + (E::F::one() - index_bit.clone()) * curr[j].clone()
        });
        let second: [E::F; N_HASH] = array::from_fn(|j| {
            index_bit.clone() * curr[j].clone()
                + (E::F::one() - index_bit.clone()) * sibling[j].clone()
        });
        let values: Vec<E::F> = chain!(
            first.into_iter(),
            second.into_iter(),
            hash.clone().into_iter()
        )
        .collect();
        eval.add_to_relation(RelationEntry::new(poseidon_elements, mult.clone(), &values));
        curr = hash.clone();
    }
}

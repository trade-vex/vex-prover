use crate::{
    executor::{flatten_single, instruction::IMTOperation},
    imt::{
        leaf::Leaf,
        side::{Buy, Sell},
    },
};
use itertools::chain;
use num_traits::{One, Zero};
use std::array;
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::{
    components::{poseidon::PoseidonElements, Claim},
    executor::instruction::{Instruction, InstructionElements},
    flatten,
    hash::{N_HASH, N_STATE},
    imt::{
        leaf::LeafColumn,
        side::{OrderSide, Side},
        IndexBits, LeafFelts, MerklePath, MerkleProof, MERKLE_HEIGHT, N_U64_FELTS,
    },
};

use super::DeletionsColumn;

/// Deletions evaluation helper
pub struct DeletionsEval<S: OrderSide> {
    pub poseidon_elements: PoseidonElements,
    pub instruction_elements: InstructionElements,
    pub claim: Claim<DeletionsColumn>,
    pub phantom: std::marker::PhantomData<S>,
}

/// This implementation of the `FrameworkEval` trait for `DeletionsEval` provides methods to evaluate
/// constraints on Deletions from Buy and Sell IMT;
///
/// # Constraint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///  Deletion Operation happens in two steps
///  1) Find the target leaf to delete
///  2) Update the parent leaf's "next" value to point to the target's "next"
///  3) Clear the target leaf (set to inactive)
///  The constraints must ensure that the deletion is done correctly.
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row  //
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row. //
///   3. Assert that the opcode is equal to the Deletion opcode. //
///   4. Assert that the target leaf is active. //
///   5. Assert that the parent leaf is active.

///   6. Assert that the initial state's root hash is equal to the root hash in the merkle path of the target leaf. --
///   7. Verify the Merkle Proof of the Target Leaf. //
///   8. Verify the Merkle Proof of the Parent Leaf. //
///   9. Assert that the parent leaf's "next" points to the target leaf. //
///  10. Update the Parent Leaf's next value to be the target leaf's next value. //
///  11. Ensure that the resultant root hash from updating the parent leaf is consistent. //
///  12. Set the target leaf to inactive // and verify its Merkle proof.
///  13. Ensure that the final state's count is equal to the initial state's count plus 1. //
///  14. Verify that the final root hash of the final state is equal to the root hash in the merkle path. --
///  15. The Priority must be updated if the target leaf was the first leaf in the tree. //
///        - If the first leaf is being deleted, the priority becomes the next leaf's priority.
///  16. Yield the Results by adding the values to the ProcessorLookupElements.   //
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///  17. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`. //
///

impl<S: OrderSide> FrameworkEval for DeletionsEval<S> {
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
        eval.add_constraint(op.opcode.clone() - E::F::from(S::op_code(IMTOperation::Deletion)));
        let mult = E::EF::from(op.is_real.clone());

        // low_leaf must be active
        eval.add_constraint(E::F::one() - op.low_leaf[0].clone());
        // target_leaf (leaf) must be active
        eval.add_constraint(E::F::one() - op.leaf[0].clone());

        // Verify that prev leaf's next points to target leaf
        // We check that the "next" field of prev leaf contains the price-time of the target leaf
        for i in 0..2 * N_U64_FELTS {
            eval.add_constraint(
                op.low_leaf[LeafColumn::NEXT + i].clone() - op.leaf[LeafColumn::PRICE + i].clone(),
            );
        }

        // eval low_leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.low_merkle_path.clone(),
            op.low_leaf.clone(),
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // Create updated low_leaf with next pointer updated to target's next pointer
        let mut updated_low_leaf = op.low_leaf.clone();
        updated_low_leaf[LeafColumn::NEXT..].clone_from_slice(&op.leaf[LeafColumn::NEXT..]);

        // eval updated low_leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.updated_low_merkle_path.clone(),
            updated_low_leaf,
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // the resultant root hash from updating low_leaf must be equal the path of deleted leaf
        // this ensures that both leaf updates are consistent
        for i in 0..N_HASH {
            eval.add_constraint(
                op.updated_low_merkle_path[MERKLE_HEIGHT][i].clone()
                    - op.merkle_path[MERKLE_HEIGHT][i].clone(),
            );
        }

        // eval target_leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.merkle_path.clone(),
            op.leaf.clone(),
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        let mut inactive_target_leaf = op.leaf.clone();
        inactive_target_leaf[LeafColumn::ACTIVE] = E::F::zero(); // Set active flag to false (0)

        // 13. eval inactive target leaf's merkle proof (replacing the original target leaf)
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),        // Proof uses the same slot
            op.updated_merkle_path.clone(), // Path reflecting the inactive leaf state
            inactive_target_leaf,           // The modified (inactive) target leaf
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone().into(), // Pass EF type
        );

        // ensure that the state count is updated correctly (incremented by 1)
        eval.add_constraint(op.final_state.n.clone() - op.initial_state.n.clone() - E::F::one());

        match S::side() {
            Side::Buy => {
                // initial state's buy root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.buy_root_hash[i].clone()
                            - op.merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // final state's buy root hash must be equal to the root in the updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.buy_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the sell IMT priority must remain unchanged
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.sell_imt_priority[i].clone()
                            - op.final_state.sell_imt_priority[i].clone(),
                    );
                }

                // For the Buy side
                let first_leaf_price_time = Leaf::<E::F, Buy>::first_price_time_felts();
                let low_leaf_is_first: [E::F; 2 * N_U64_FELTS] = array::from_fn(|i| {
                    op.low_leaf[LeafColumn::PRICE + i].clone() - first_leaf_price_time[i].clone()
                });

                // If the low_leaf is the first leaf (i.e., target leaf is next of first leaf),
                // the priority must be updated to the target leaf's next
                for i in 0..2 * N_U64_FELTS {
                    // Check if priority changed
                    let priority_changed = op.final_state.buy_imt_priority[i].clone()
                        - op.initial_state.buy_imt_priority[i].clone();

                    // If priority changed, then low_leaf must be the first leaf
                    eval.add_constraint(priority_changed.clone() * low_leaf_is_first[i].clone());

                    // If priority changed, new priority must be the target's next
                    eval.add_constraint(
                        priority_changed.clone()
                            * (op.final_state.buy_imt_priority[i].clone()
                                - op.leaf[LeafColumn::NEXT_PRICE + i].clone()),
                    );
                }
            }
            Side::Sell => {
                // initial state's sell root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.sell_root_hash[i].clone()
                            - op.merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // final state's sell root hash must be equal to the root in the updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.sell_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the buy IMT priority must remain unchanged
                for i in 0..2 * N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.buy_imt_priority[i].clone()
                            - op.final_state.buy_imt_priority[i].clone(),
                    );
                }

                // For the Sell side
                let first_leaf_price_time = Leaf::<E::F, Sell>::first_price_time_felts();
                let low_leaf_is_first: [E::F; 2 * N_U64_FELTS] = array::from_fn(|i| {
                    op.low_leaf[LeafColumn::PRICE + i].clone() - first_leaf_price_time[i].clone()
                });

                // If the low_leaf is the first leaf (i.e., target leaf is next of first leaf),
                // the priority must be updated to the target leaf's next
                for i in 0..2 * N_U64_FELTS {
                    // Check if priority changed
                    let priority_changed = op.final_state.sell_imt_priority[i].clone()
                        - op.initial_state.sell_imt_priority[i].clone();

                    // If priority changed, then low_leaf must be the first leaf
                    eval.add_constraint(priority_changed.clone() * low_leaf_is_first[i].clone());

                    // If priority changed, new priority must be the target's next
                    eval.add_constraint(
                        priority_changed.clone()
                            * (op.final_state.sell_imt_priority[i].clone()
                                - op.leaf[LeafColumn::NEXT_PRICE + i].clone()),
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
    let leaf: Vec<E::F> = leaf[0..N_STATE].try_into().unwrap();
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

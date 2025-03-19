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

use super::UpdateColumn;

#[derive(Clone)]
pub struct VolumeUpdateEval<S> {
    pub claim: Claim<UpdateColumn>,
    pub poseidon_elements: PoseidonElements,
    pub instruction_elements: InstructionElements,
    pub _side: PhantomData<S>,
}

/// This implementation of the `FrameworkEval` trait for `VolumeUpdateEval` provides methods to evaluate
/// constraints on Volume Updates to Buy and Sell IMT;
///
/// # Constraint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///  Volume Update Operation happens in one step:
///  1) Updating the existing leaf's volume value
///  The constraints must ensure that the updates are done correctly without changing other properties of the leaf.
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. Assert that the opcode is equal to the Update opcode.
///   4. Assert that the initial root hash of the initial state is equal to the root hash in the merkle path. ( C6 of insertions )
///   5. Assert that the leaf being updated is active.
///   6. The leaf is part of the Merkle Tree by verifying the Merkle Proof.
///      - The Merkle Proof is a list of sibling hashes from the leaf to the root.
///      - The Merkle Path is a list of hashes from the leaf to the root.
///      - IndexBits is the binary representation of the index of the leaf.
///   7. Update the leaf's volume value only without changing other leaf properties
///   8. Verify the Merkle Proof of the updated leaf.
///   9. Ensure that the final state's count is equal to the initial state's count (no new leaves).
///   10. Verify that the final root hash of the final state is equal to the root hash in the merkle path of the updated leaf.
///   11. Yield the Results by adding the values to the ProcessorLookupElements.   
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///   12. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
impl<S: OrderSide> FrameworkEval for VolumeUpdateEval<S> {
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
        eval.add_constraint(op.opcode.clone() - E::F::from(S::op_code(IMTOperation::Update)));

        let mult = E::EF::from(op.is_real.clone());

        // leaf must be active 
        eval.add_constraint(E::F::one() - op.leaf[0].clone());

        // ensure we're not updating the first/last sentinel leaves
        let first_price_time = Leaf::<E::F, S>::first_price_time_felts();
        let is_first_leaf = op.leaf[LeafColumn::PRICE..(LeafColumn::PRICE + 2 * N_U64_FELTS)]
            .iter()
            .zip(first_price_time.iter())
            .map(|(a, b)| a.clone() - b.clone())
            .fold(E::F::zero(), |acc, diff| acc + diff * diff);
        eval.add_constraint(is_first_leaf.clone());

        // eval leaf's merkle proof - this verifies the leaf exists in the tree
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.merkle_path.clone(),
            op.leaf.clone(),
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        match S::side() {
            Side::Buy => {
                // initial state's buy root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.buy_root_hash[i].clone()
                            - op.merkle_path[MERKLE_HEIGHT][i].clone(),
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
            }
        }

        // create updated leaf with new volume
        let mut updated_leaf = op.leaf.clone();
        // volume is at positions LeafColumn::VOLUME through LeafColumn::VOLUME + N_U64_FELTS
        updated_leaf[LeafColumn::VOLUME..(LeafColumn::VOLUME + N_U64_FELTS)]
            .clone_from_slice(&op.leaf[1..9]);

        // eval updated leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.updated_merkle_path.clone(),
            updated_leaf,
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // ensure that the state count remains unchanged
        eval.add_constraint(op.final_state.n.clone() - op.initial_state.n.clone());

        // ensure priorities remain unchanged
        for i in 0..2 * N_U64_FELTS {
            // buy IMT priority doesn't change
            eval.add_constraint(
                op.initial_state.buy_imt_priority[i].clone()
                    - op.final_state.buy_imt_priority[i].clone(),
            );
            // sell IMT priority doesn't change
            eval.add_constraint(
                op.initial_state.sell_imt_priority[i].clone()
                    - op.final_state.sell_imt_priority[i].clone(),
            );
        }

        match S::side() {
            Side::Buy => {
                // final state's buy root hash must be equal to the root in the updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.buy_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
                // sell root hash shouldn't change
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.sell_root_hash[i].clone()
                            - op.final_state.sell_root_hash[i].clone(),
                    );
                }
            }
            Side::Sell => {
                // final state's sell root hash must be equal to the root in the updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.sell_root_hash[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
                // buy root hash shouldn't change
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.buy_root_hash[i].clone()
                            - op.final_state.buy_root_hash[i].clone(),
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

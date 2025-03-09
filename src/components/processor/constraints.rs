use crate::executor::flatten_single;
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

use super::ProcessorColumn;

#[derive(Clone)]
pub struct ProcessorEval<S> {
    pub claim: Claim<ProcessorColumn>,
    pub less_than_elements: LessThanElements,
    pub strict_less_than_elements: StrictLessThanElements,
    pub instruction_elements: InstructionElements,
    pub _side: PhantomData<S>,
}

/// This implementation of the `FrameworkEval` trait for `ProcessorEval` provides methods to evaluate
/// constraints on state changes in a single Instruction.
/// 
/// The State consists of the following columns:
/// - InitialState = i, where i is the index of the state.
/// - InitialBuyRootHash, // root hash of the Buy IMT
/// - InitialBuyIMTPriority, // the order which should be matched first in the Buy IMT
/// - InitialSellRootHash, // root hash of the Sell IMT
/// - InitialSellIMTPriority, // the order which should be matched first in the Sell IMT
/// - FinalState = i + 1, where i is the index of the state.
/// - FinalBuyRootHash, // root hash of the Buy IMT
/// - FinalBuyIMTPriority, // the order which should be matched first in the Buy IMT
/// - FinalSellRootHash, // root hash of the Sell IMT
/// - FinalSellIMTPriority, // the order which should be matched first in the Sell IMT
///
/// The state transition is represented by the Instruction column.
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
///   3. Assert that the inserted leaf's priority lies b/w the low leaf and low leaf's next.
///      - The priority is calculated by the first 16 bytes of the leaf.
///   4. The Low leaf is part of the Merkle Tree by verifying the Merkle Proof.
///      - The Merkle Proof is a list of sibling hashes from the leaf to the root.
///      - The Merkle Path is a list of hashes from the leaf to the root.
///      - IndexBits is the binary representation of the index of the leaf.
///   5. Update the Low Leaf's next value by replacing the "next" value with the "label" of the leaf being inserted
///   6. Ensure that the resultant root hash from updating the low leaf is equal to the root contained in inactive leaf's merkle path.
///   7. Verify the Merkle Proof of the Inactive Leaf.
///   8. Update the Inactive Leaf's value to the leaf in the trace.
///   9. Yield the Results by adding the values to the ProcessorLookupElements.   
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///   10. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
///
///
/// Note: Add leaf's next constraint!
impl<S: OrderSide> FrameworkEval for ProcessorEval<S> {
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

        let mult = E::EF::from(op.is_real.clone());

        eval.finalize_logup();
        eval
    }
}

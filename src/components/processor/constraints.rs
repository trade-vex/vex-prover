use crate::executor::{flatten_single, state::StateElements};
use num_traits::One;
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::{
    components::Claim,
    executor::instruction::{Instruction, InstructionElements},
    flatten,
};

use super::ProcessorColumn;

#[derive(Clone)]
pub struct ProcessorEval {
    pub claim: Claim<ProcessorColumn>,
    pub state_elements: StateElements,
    pub instruction_elements: InstructionElements,
}

/// This implementation of the `FrameworkEval` trait for `ProcessorEval` provides methods to evaluate
/// constraints on Main Trace/Processor component.
///
/// # Constaint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. Use the initial state, which was yielded by the previous row.
///         - the first state is not yielded by any row
///         - the end state is yielded by the last row and not used by any row
///         - The sum for this component will be non zero x
///         - zero = x - initial_state + final_state
///  4. Use the instruction elements to update the state to the final state.
///  5. Ensure that the state count is updated correctly.
///  6. Yield the final state.  
///  7. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
impl FrameworkEval for ProcessorEval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 2  // Raised to +2 to match Poseidon and enable better batching
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let op = Instruction::<E::F>::from_eval(&mut eval);

        // is_real must be a boolean
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));

        let is_real = op.is_real.clone();
        let mult = E::EF::from(is_real.clone());

        let initial_state: Vec<E::F> = flatten!(
            op.initial_state.n.clone(),
            op.initial_state.buy_root.clone(),
            op.initial_state.best_buy_price.clone(),
            op.initial_state.sell_root.clone(),
            op.initial_state.best_sell_price.clone(),
            op.initial_state.op_code.clone()
        );

        // use the initial state
        eval.add_to_relation(RelationEntry::new(
            &self.state_elements,
            mult.clone(),
            &initial_state,
        ));

        let values: Vec<E::F> = flatten!(
            op.initial_state.n.clone(),
            op.initial_state.buy_root,
            op.initial_state.best_buy_price,
            op.initial_state.sell_root,
            op.initial_state.best_sell_price,
            op.initial_state.op_code,
            op.opcode.clone(),
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
            op.final_state.n.clone(),
            op.final_state.buy_root.clone(),
            op.final_state.best_buy_price.clone(),
            op.final_state.sell_root.clone(),
            op.final_state.best_sell_price.clone(),
            op.final_state.op_code.clone(),
            op.is_real
        );
        // use the instruction elements to update the state to the final state
        eval.add_to_relation(RelationEntry::new(
            &self.instruction_elements,
            mult.clone(),
            &values,
        ));

        // ensure that the state count is updated correctly
        // TODO: This should respect is_real (n should only increment for non-padded rows)
        // However, changing to `- is_real` requires updating trace generation to ensure
        // all padded rows have final_state == initial_state, not just for n
        eval.add_constraint(op.final_state.n.clone() - op.initial_state.n.clone() - E::F::one());

        // the instructions opcode must be the same as the final state opcode
        eval.add_constraint(op.opcode.clone() - op.final_state.op_code.clone());

        let final_state: Vec<E::F> = flatten!(
            op.final_state.n,
            op.final_state.buy_root,
            op.final_state.best_buy_price,
            op.final_state.sell_root,
            op.final_state.best_sell_price,
            op.final_state.op_code
        );

        // yield the final state
        eval.add_to_relation(RelationEntry::new(
            &self.state_elements,
            -mult.clone(),
            &final_state,
        ));

        // the inital and final state relations are batched in pairs in the first interaction column
        // the instruction elements are in the second interaction column
        eval.finalize_logup_batched(&vec![0, 1, 0]);
        eval
    }
}

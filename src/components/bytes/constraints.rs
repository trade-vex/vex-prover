use stwo_prover::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
};

use crate::components::Claim;

use super::{
    BytesPreProcessedColumn, LessThanU8Elements, RangeCheckU8Elements, LOG_SIZE,
};

pub type BytesComponent = FrameworkComponent<BytesEval>;

pub struct BytesEval {
    pub claim: Claim<BytesPreProcessedColumn>,
    pub less_than_u8_elements: LessThanU8Elements,
    pub range_check_u8_elements: RangeCheckU8Elements,
}

/// This implementation of the `FrameworkEval` trait for `BytesEval` provides methods to evaluate
/// constraints on byte operations. The primary purpose of this
/// implementation is to evaluate specific constraints related to bitwise comparisons 
/// and range checks on byte values.
///
/// # Constaint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///   This method performs the actual evaluation of constraints. It retrieves preprocessed columns
///   for the byte values and then adds Interaction Constraints to
///   the evaluation table. The constraints evaluated are:
///   - Comparison of two byte values to check if one is less than the other.
///   - Range check to ensure byte values are within the valid range (0-255).
///
///   The method follows these steps:
///   1. Retrieve preprocessed columns for byte values `a` and `b`, and their corresponding constraints
///      `c_less_than` (for less-than comparison).
///   2. Retrieve Multiplicities `less_than_u8_mult` and `range_check_u8_mult`.
///   3. Add the constraints to the evaluation table using `eval.add_to_relation` method:
///      - For less-than comparison: Adds a relation entry with `a`, `b`, and `c_less_than`.
///      - For range check: Adds a relation entry with `a` and `b`.
///        The Multiplicity is set to `-range_check_u8_mult` as this Table is used to "yield"
///        values which are "used" by other component that "lookup" the values.
///        It Has to be ensured that the LogUp Entries are added in the same order as the
///        Interaction Trace.
///   4. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
/// The bytes evaluation table is used to ensure that the byte operations adhere to the PreProcessed Table,
/// whose commitment is known to verifier prior to the proof generation.
impl FrameworkEval for BytesEval {
    fn log_size(&self) -> u32 {
        LOG_SIZE
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        LOG_SIZE + 2  // Raised to +2 to match Poseidon and enable better batching
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Retrieve preprocessed columns
        let a = eval.get_preprocessed_column(BytesPreProcessedColumn::A.preprocessed_id());
        let b = eval.get_preprocessed_column(BytesPreProcessedColumn::B.preprocessed_id());
        let c_less_than =
            eval.get_preprocessed_column(BytesPreProcessedColumn::CLessThanU8.preprocessed_id());

        // Retrieve Multiplicities
        let less_than_u8_mult = eval.next_trace_mask();
        let range_check_u8_mult = eval.next_trace_mask();

        // Yields a < b = c_less_than
        eval.add_to_relation(RelationEntry::new(
            &self.less_than_u8_elements,
            E::EF::from(-less_than_u8_mult),
            &[a.clone(), b.clone(), c_less_than.clone()],
        ));

        // Yields a, b < 256
        eval.add_to_relation(RelationEntry::new(
            &self.range_check_u8_elements,
            E::EF::from(-range_check_u8_mult),
            &[a.clone(), b.clone()],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

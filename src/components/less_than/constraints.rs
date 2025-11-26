use itertools::{chain, izip};
use num_traits::{One, Zero};
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::components::{bytes::LessThanU8Elements, Claim};

use super::{LessThanColumn, LessThanElements, LessThanOp, StrictLessThanElements};

#[derive(Clone)]
pub struct LessThanEval {
    pub claim: Claim<LessThanColumn>,
    pub less_than_u8_elements: LessThanU8Elements,
    pub less_than_elements: LessThanElements,
    pub strict_less_than_elements: StrictLessThanElements,
}

/// This implementation of the `FrameworkEval` trait for `LessThanEval` provides methods to evaluate
/// constraints on less than operations. The primary purpose of this
/// implementation is to evaluate specific constraints related to less than operations used by other components.
///
/// # Constraint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///   It retrieves the LessThanOp for a particular row, each row represents a single less than operation.
///
///   The method follows these steps:
///   1. Retrieve LessThanOp for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. Each flag must be a boolean. The sum of flags must be either 0 or 1.
///      Flag represents an array of booleans, has one elment set to true if a_byte is not equal to b_byte.
///   4. The sum of flags must be either 0 or 1. 0 if a is equal to b, 1 if a is not equal to b.
///   5. Loop through each byte of a and b, and add constraints:
///        if inequality is not visited yet then a_byte must be equal to b_byte and record the first byte where a is not equal to b.
///   6. Add constraints for a_comparison_byte and b_comparison_byte.
///   7. The Result of the Operation op.c must be a boolean.
///   8. The Result of the Operation op.c must be 1 if a_comparison_byte is less than b_comparison_byte
///      which is checked by looking up the result of the comparison bytes from the less_than_u8_elements
///      from the PreProcessedBytes Table.
///        - Multiplicity of the relation is the is_real flag.
///        - Values are a_comparison_byte, b_comparison_byte, and c.
///   9. Yield the Results by adding the values to the less_than_elements.   
///        - Multiplicity of the relation is the negation of is_real flag.
///        - Values are a, b, and c.
///   10. Finalize the evaluation by calling `eval.finalize_logup_batched()`.
impl FrameworkEval for LessThanEval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 2  // Raised to +2 to match Poseidon and enable better batching
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let op = LessThanOp::<E::F>::from_eval(&mut eval);

        // is_real must be a boolean
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));
        // is_strict must be a boolean
        eval.add_constraint(op.is_strict.clone() * (op.is_strict.clone() - E::F::one()));
        // Each flag must be boolean
        let mut sum_flags = E::F::zero();
        for flag in op.flags.iter() {
            eval.add_constraint(flag.clone() * (E::F::one() - flag.clone()));
            sum_flags = sum_flags.clone() + flag.clone();
        }
        // sum must be either 0 or 1
        // 0 if a is equal to b
        // 1 if a is not equal to b
        eval.add_constraint(sum_flags.clone() * (E::F::one() - sum_flags.clone()));

        // a_comparison_byte and b_comparison_byte must be equal to the first bytes where a[i] is not equal to b[i]
        let mut is_inequality_visited = E::F::zero();
        let mut a_comparison_byte = E::F::zero();
        let mut b_comparison_byte = E::F::zero();
        for (a_byte, b_byte, flag) in izip!(
            op.a.clone().into_iter().rev(),
            op.b.clone().into_iter().rev(),
            op.flags.into_iter().rev()
        ) {
            is_inequality_visited = is_inequality_visited.clone() + flag.clone();
            a_comparison_byte = a_comparison_byte.clone() + a_byte.clone() * flag.clone();
            b_comparison_byte = b_comparison_byte.clone() + b_byte.clone() * flag;

            // if inequality is not visited yet then a_byte must be equal to b_byte
            eval.add_constraint(
                (E::F::one() - is_inequality_visited.clone()) * (a_byte.clone() - b_byte.clone()),
            );
        }
        eval.add_constraint(op.a_comparison_byte.clone() - a_comparison_byte.clone());
        eval.add_constraint(op.b_comparison_byte.clone() - b_comparison_byte.clone());

        // c must be a boolean
        eval.add_constraint(op.c.clone() * (op.c.clone() - E::F::one()));

        // if a and b are equal i.e sum_flags is 0
        // is_inequality_visited must be 0
        // a_comparison_byte must be 0
        // b_comparison_byte must be 0
        eval.add_constraint((E::F::one() - sum_flags.clone()) * is_inequality_visited.clone());
        eval.add_constraint((E::F::one() - sum_flags.clone()) * a_comparison_byte.clone());
        eval.add_constraint((E::F::one() - sum_flags.clone()) * b_comparison_byte.clone());
        // When a == b (sum_flags == 0):
        // if strict (is_strict == 1): the result must be 0
        // if not strict (is_strict == 0): the result must be 1
        // Expected c when equal: (1 - is_strict)
        let c_expected_when_equal = E::F::one() - op.is_strict.clone();
        eval.add_constraint(
            (E::F::one() - sum_flags.clone()) * (op.c.clone() - c_expected_when_equal),
        );
        // c must be 1 if a_comparision_byte is less than b_comparison_byte
        // c must be 0 if a_comparision_byte is greater than b_comparison_byte
        // Look Up if the c has been set correctly and "use" the result of the comparison bytes
        // If strict, the result must be 1 if a_comparision_byte is less than b_comparison_byte
        // the less_than_u8_elements result is strictly 1 if a_comparision_byte is less than b_comparison_byte
        // therefore if a is equal to b, the result for less_than_u8_elements must be 0
        // For strict: c_for_u8 = op.c
        // For non-strict: c_for_u8 = sum_flags * op.c (0 when a == b)
        // Combined: c_for_u8 = is_strict * op.c + (1 - is_strict) * sum_flags * op.c
        let c_for_u8 = op.is_strict.clone() * op.c.clone()
            + (E::F::one() - op.is_strict.clone()) * sum_flags.clone() * op.c.clone();
        eval.add_to_relation(RelationEntry::new(
            &self.less_than_u8_elements,
            E::EF::from(op.is_real.clone()),
            &[op.a_comparison_byte, op.b_comparison_byte, c_for_u8],
        ));

        // Yield the Results
        let values: Vec<E::F> =
            chain!(op.a.into_iter(), op.b.into_iter(), std::iter::once(op.c)).collect();
        // Yield to strict_less_than_elements when is_strict == 1
        eval.add_to_relation(RelationEntry::new(
            &self.strict_less_than_elements,
            -E::EF::from(op.is_real.clone() * op.is_strict.clone()),
            &values,
        ));
        // Yield to less_than_elements when is_strict == 0
        eval.add_to_relation(RelationEntry::new(
            &self.less_than_elements,
            -E::EF::from(op.is_real.clone() * (E::F::one() - op.is_strict.clone())),
            &values,
        ));
        // Batch: column 0 has less_than_u8_elements, column 1 has both yield relations
        eval.finalize_logup_batched(&vec![0, 1, 1]);
        eval
    }
}

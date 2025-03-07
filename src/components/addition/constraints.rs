use itertools::chain;
use num_traits::One;
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use super::{AddColumn, AddElements, AddOp};
use crate::components::{bytes::RangeCheckU8Elements, Claim};
use crate::types::N_U64_LIMBS;
use stwo_prover::core::fields::m31::BaseField;
/// AddEval implements the constraint evaluation logic for addition operations.

/// Claim about the trace, including log size and other properties
/// Relation for checking byte-wise addition correctness
/// Relation for storing and verifying complete addition results
#[derive(Clone)]
pub struct AddEval {
    pub claim: Claim<AddColumn>,
    pub range_check_u8_elements: RangeCheckU8Elements,
    pub add_elements: AddElements,
}

/// This implementation of the `FrameworkEval` trait for `AddEval` provides methods to evaluate
/// constraints on addition operations. The primary purpose of this
/// implementation is to evaluate specific constraints related to addition operations used by other components.
///
/// # Constraint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///   It retrieves the AddOp for a particular row, each row represents a single addition operation.
/// Primary method for evaluating constraints on an addition operation
///
/// This method performs a comprehensive set of checks:
/// 1. Validate the "is_real" flag
/// 2. Check byte-wise addition with carry
/// 3. Ensure carry bits are boolean
/// 4. Perform U8 range checks
/// 5. Generate interaction relations
/// Implementation of constraint evaluation for addition operations.
///
/// This implementation provides methods to:
/// 1. Check the integrity of addition operations
/// 2. Validate carry propagation
/// 3. Ensure byte-level constraints are met
/// 4. Perform range checks on input and output bytes

impl FrameworkEval for AddEval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    /// Computes the maximum constraint degree bound
    /// This helps in polynomial commitment scheme and constraint verification
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // Extract the addition operation details from the current row
        let op = AddOp::<E::F>::from_eval(&mut eval);

        // Base value for overflow check (256 in the field)
        let base = E::F::from(BaseField::from(256));

        // CONSTRAINT 1: Validate "is_real" flag
        // Ensure the flag is a boolean (0 or 1)
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));

        // CONSTRAINT 2: Byte-wise addition with carry constraints
        // First byte addition (no incoming carry)
        let overflow_0 = op.a[0].clone() + op.b[0].clone() - op.c[0].clone();

        // Ensure overflow is either 0 or 256
        eval.add_constraint(overflow_0.clone() * (overflow_0.clone() - base.clone()));

        // Validate carry for the first byte
        // If carry is 1, overflow must be 256
        // If carry is 0, overflow must be 0
        eval.add_constraint(op.carry[0].clone() * (overflow_0.clone() - base.clone()));
        eval.add_constraint((op.carry[0].clone() - E::F::one()) * overflow_0);

        // CONSTRAINT 3: Middle bytes addition with carry propagation
        // Check each intermediate byte addition, ensuring correct carry handling
        for i in 1..N_U64_LIMBS - 1 {
            let overflow_i =
                op.a[i].clone() + op.b[i].clone() + op.carry[i - 1].clone() - op.c[i].clone();

            // Ensure overflow is either 0 or 256
            eval.add_constraint(overflow_i.clone() * (overflow_i.clone() - base.clone()));

            // Validate carry for intermediate bytes
            eval.add_constraint(op.carry[i].clone() * (overflow_i.clone() - base.clone()));
            eval.add_constraint((op.carry[i].clone() - E::F::one()) * overflow_i);
        }

        // CONSTRAINT 4: Last byte addition (with incoming carry, no outgoing carry)
        let last_index = N_U64_LIMBS - 1;
        let overflow_last =
            op.a[last_index].clone() + op.b[last_index].clone() + op.carry[last_index - 1].clone()
                - op.c[last_index].clone();

        // Ensure last byte overflow is either 0 or 256
        eval.add_constraint(overflow_last.clone() * (overflow_last - base));

        // CONSTRAINT 5: Ensure all carry bits are boolean (0 or 1)
        for i in 0..N_U64_LIMBS - 1 {
            eval.add_constraint(op.carry[i].clone() * (op.carry[i].clone() - E::F::one()));
        }

        let values: Vec<E::F> =
            chain!(op.a.into_iter(), op.b.into_iter(), op.c.into_iter()).collect();

        // 5. todo: add range checks for a[i], b[i], c[i]
        for i in (0..24).step_by(4) {
            eval.add_to_relation(RelationEntry::new(
                &self.range_check_u8_elements,
                E::EF::from(op.is_real.clone()),
                &[values[i].clone(), values[i + 1].clone()],
            ));
            eval.add_to_relation(RelationEntry::new(
                &self.range_check_u8_elements,
                E::EF::from(op.is_real.clone()),
                &[values[i + 2].clone(), values[i + 3].clone()],
            ));
        }

        // // CONSTRAINT 7: Yield the complete addition results
        // Add a, b, c, and carry values in the same order as in interaction_trace.rs
        eval.add_to_relation(RelationEntry::new(
            &self.add_elements,
            -E::EF::from(op.is_real.clone()),
            &values,
        ));
        // Finalize the logup (logarithmic lookup) in pairs
        eval.finalize_logup_in_pairs();
        eval
    }
}

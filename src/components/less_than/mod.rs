use crate::types::N_U64_LIMBS;
use std::array;
use stwo_prover::{
    constraint_framework::EvalAtRow,
    core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE},
    relation,
};

use super::TraceSize;
mod constraints;
mod trace;

pub use trace::{interaction_trace, preprocessed_trace, trace};

/// Less Than Operations
pub type LessThanOperations = Vec<[BaseField; LessThanColumn::MAIN_COLS]>;

/// LessThanOp represents the LessThan operation between two uint represented as N u8 limbs.
/// Example for BaseField = M31 and uint64_t: N = 8
#[derive(Debug)]
pub struct LessThanOp<F> {
    // first operand
    a: [F; N_U64_LIMBS],
    // second operand
    b: [F; N_U64_LIMBS],
    // result of the comparison
    c: F,
    // flag is 1 for the most significant byte where a[i] is not equal to b[i]
    flags: [F; N_U64_LIMBS],
    // First byte of the first operand where a[i] is not equal to b[i] from the most significant byte
    a_comparison_byte: F,
    // First byte of the second operand where a[i] is not equal to b[i] from the most significant byte
    b_comparison_byte: F,
    // is real flag to check if the operation is not among the dummy padded operations
    is_real: F,
}

impl<F> LessThanOp<F> {
    /// from_eval returns a LessThanOp instance from a given EvalAtRow instance
    fn from_eval<E: EvalAtRow>(eval: &mut E) -> LessThanOp<E::F> {
        let a = array::from_fn(|_| eval.next_trace_mask());
        let b = array::from_fn(|_| eval.next_trace_mask());
        let c = eval.next_trace_mask();
        let flags = array::from_fn(|_| eval.next_trace_mask());
        let a_comparison_byte = eval.next_trace_mask();
        let b_comparison_byte = eval.next_trace_mask();
        let is_real = eval.next_trace_mask();
        LessThanOp {
            a,
            b,
            c,
            flags,
            a_comparison_byte,
            b_comparison_byte,
            is_real,
        }
    }
}

/// LessThanColumn represents a Column for the starting limb of a field in LessThanOp
#[derive(Debug, Clone)]
pub struct LessThanColumn;

impl LessThanColumn {
    pub const A: usize = 0;
    pub const B: usize = Self::A + N_U64_LIMBS;
    pub const C: usize = Self::B + N_U64_LIMBS;
    pub const FLAGS: usize = Self::C + 1;
    pub const A_COMPARISON_BYTE: usize = Self::FLAGS + N_U64_LIMBS;
    pub const B_COMPARISON_BYTE: usize = Self::A_COMPARISON_BYTE + 1;
    pub const IS_REAL: usize = Self::B_COMPARISON_BYTE + 1;
}

impl TraceSize for LessThanColumn {
    // last field's index + offset
    const MAIN_COLS: usize = Self::IS_REAL + 1;
    // 1 Interaction Column for LessThanU8 check
    // 1 Interaction Column for yielding the result
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

// A Total of 17 elements are "used" or "yielded" for the less than operation
// a - 8 limbs corresponding to the first operand(u64)
// b - 8 limbs corresponding to the second operand(u64)
// c - 1 limb corresponding to the result of the comparison
relation!(LessThanElements, 17);

#[cfg(test)]
mod tests {
    use constraints::LessThanEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::bytes::LessThanU8Elements, executor::record::ExecutionTrace, types::Price,
    };

    use super::*;

    #[test_log::test]
    fn test_less_than_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let mut record = ExecutionTrace::new();
        let n = 1242132;
        let mut rng = rand::thread_rng();
        for _ in 0..n {
            let a: Price<BaseField> = Price::from_u64(rng.gen());
            let b: Price<BaseField> = Price::from_u64(rng.gen());
            record.add_less_than_event(a.to_felts(), b.to_felts()).unwrap();
        }
        let log_size = (record.less_than_operations.len() - 1).ilog2() + 1;
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let less_than_u8_elements = LessThanU8Elements::draw(&mut channel);
        let less_than_elements = LessThanElements::draw(&mut channel);

        // Trace Generation
        let span = span!(Level::INFO, "Trace Generation").entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace(record.less_than_operations);
        let (interaction_trace, interaction_claim) =
            interaction_trace(&trace, &less_than_u8_elements, &less_than_elements);
        span.exit();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component = LessThanEval {
            less_than_u8_elements,
            less_than_elements,
            claim,
        };

        // panics if the constraints are not satisfied
        let _span = span!(Level::INFO, "Constraint Assertion").entered();
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(log_size),
            |eval| {
                component.evaluate(eval);
            },
            interaction_claim.claimed_sum,
        )
    }
}

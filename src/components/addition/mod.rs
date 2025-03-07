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

/// AddOperations represents a collection of add operations to be processed in the circuit.
/// Each operation is represented as an array of field elements arranged according to the AddColumn layout.
pub type AddOperations = Vec<[BaseField; AddColumn::MAIN_COLS]>;

/// AddOp represents a single addition operation between two unsigned integers,
/// represented as N u8 limbs (where N is typically 8 for uint64_t).
///
/// The structure captures all the details needed to validate the addition:
/// - Input operands (a and b)
/// - Result of addition (c)
/// - Carry bits for each byte (except the last byte)
/// - A flag to distinguish real operations from padding
#[derive(Debug)]
pub struct AddOp<F> {
    /// First input operand, represented as an array of N limbs
    a: [F; N_U64_LIMBS],

    /// Second input operand, represented as an array of N limbs
    b: [F; N_U64_LIMBS],

    /// Result of the addition, represented as an array of N limbs
    c: [F; N_U64_LIMBS],

    /// Carry bits for intermediate byte additions (N_U64_LIMBS - 1 carries)
    /// Each carry represents whether the previous byte addition resulted in an overflow
    carry: [F; N_U64_LIMBS - 1],

    /// Flag to indicate if this is a "real" operation or a padding operation
    /// Helps distinguish between actual computations and dummy rows added for trace alignment
    is_real: F,
}

impl<F> AddOp<F> {
    /// Extracts an AddOp instance from an evaluation row.
    ///
    /// This method is used during constraint evaluation to retrieve the
    /// field elements representing the addition operation.
    ///
    /// # Parameters
    /// - `eval`: An evaluation context that allows sequential access to trace masks
    ///
    /// # Returns
    /// An AddOp struct with field elements extracted from the evaluation context
    fn from_eval<E: EvalAtRow>(eval: &mut E) -> AddOp<E::F> {
        // Extract field elements for each component of the addition operation
        let a = array::from_fn(|_| eval.next_trace_mask());
        let b = array::from_fn(|_| eval.next_trace_mask());
        let c = array::from_fn(|_| eval.next_trace_mask());
        let carry = array::from_fn(|_| eval.next_trace_mask());
        let is_real = eval.next_trace_mask();

        AddOp {
            a,
            b,
            c,
            carry,
            is_real,
        }
    }
}

/// AddColumn defines the layout of columns in the trace for an addition operation.
///
/// This struct provides indices for different components of the addition operation,
/// ensuring a consistent and structured representation of the trace.
#[derive(Debug, Clone)]
pub struct AddColumn;

impl AddColumn {
    /// Starting index for the first operand (a) columns
    pub const A: usize = 0;

    /// Starting index for the second operand (b) columns
    pub const B: usize = Self::A + N_U64_LIMBS;

    /// Starting index for the result (c) columns
    pub const C: usize = Self::B + N_U64_LIMBS;

    /// Starting index for carry bits
    pub const CARRY: usize = Self::C + N_U64_LIMBS;

    /// Index for the "is real" flag column
    pub const IS_REAL: usize = Self::CARRY + (N_U64_LIMBS - 1);
}

/// Implements the TraceSize trait to define the structure of the addition trace
impl TraceSize for AddColumn {
    /// Total number of main columns for the addition operation trace
    /// Includes: a, b, c, carry, and is_real columns
    const MAIN_COLS: usize = Self::IS_REAL + 1;

    /// Number of interaction columns includes:
    /// - 1 column for AddU8 element checks
    /// - 1 column for yielding the result
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

// Defines a relation for storing and verifying addition operation elements
// The number 18 specifies the log size of the relation
relation!(AddElements, 24);

#[cfg(test)]
mod tests {
    use constraints::AddEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use super::*;
    use crate::{components::bytes::RangeCheckU8Elements, executor::record::ExecutionTrace, types::Price};

    #[test_log::test]
    fn test_addition_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let mut record = ExecutionTrace::new();
        let n = 124213;
        let mut rng = rand::thread_rng();
        for _ in 0..n {
            let a: Price<BaseField> = Price::from_u64(rng.gen());
            let b: Price<BaseField> = Price::from_u64(rng.gen());
            record.add_add_event(a.to_felts(), b.to_felts());
        }
        let log_size = (record.add_operations.len() - 1).ilog2() + 1;
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let range_check_u8_elements = RangeCheckU8Elements::draw(&mut channel);
        let add_elements = AddElements::draw(&mut channel);

        // Trace Generation
        let span = span!(Level::INFO, "Trace Generation").entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace(record.add_operations);
        let (interaction_trace, interaction_claim) =
            interaction_trace(&trace, &range_check_u8_elements, &add_elements);
        span.exit();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component = AddEval {
            range_check_u8_elements,
            add_elements,
            claim,
        };

        // Panics if the constraints are not satisfied
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

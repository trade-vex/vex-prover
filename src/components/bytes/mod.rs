use stwo_prover::{
    constraint_framework::preprocessed_columns::PreProcessedColumnId,
    core::{backend::simd::column::BaseColumn, fields::secure_column::SECURE_EXTENSION_DEGREE},
    relation,
};

use super::TraceSize;

mod constraints;
mod trace;

pub use constraints::BytesComponent;
pub use trace::{interaction_trace, preprocessed_trace, trace};

/// U8 Operations
/// Index- 0: multiplicities of and operation for a u8 pair
/// Index- 1: multiplicities of less than range checks for u8 pairs. checks a < b < 256
/// Index- 2: multiplicities of range check for a pair of u8. checks if a < 256 && b < 256
pub type ByteOperations = [BaseColumn; 3];

/// Element Bits Represents the number of bits for which the operation is pre-computed.
pub const ELEMENT_BITS: u32 = 8;

/// Log Size of the trace.
/// Number of combinations for a pair of 2 ELEMENT_BITS = 2^(ELEMENT_BITS) * 2^(ELEMENT_BITS) = 2^(2 * ELEMENT_BITS)
pub const LOG_SIZE: u32 = 2 * ELEMENT_BITS;

/// Number of PreProcessed Columns for Bytes Component.
pub const N_PREPROCESSED_COLUMNS: usize = 4;

/// Bytes Component is the PreProcessed Table for Binary Operations b/w pair of ELEMENT_BITS elements.
#[derive(Debug)]
pub enum BytesPreProcessedColumn {
    A = 0,
    B = 1,
    CAnd = 2,
    CLessThanU8 = 3,
}

impl TraceSize for BytesPreProcessedColumn {
    const MAIN_COLS: usize = 3;
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

impl BytesPreProcessedColumn {
    pub fn preprocessed_id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId {
            id: format!("preprocessed_bytes_column_{:?}", self),
        }
    }

    pub fn index(&self) -> usize {
        match self {
            Self::A => 0,
            Self::B => 1,
            Self::CAnd => 2,
            Self::CLessThanU8 => 3,
        }
    }
}

// Relation Elements for and,
// a ==> First Operand
// b ==> Second Operand
// c_and ==> a & b
// c_less_than ==> a < b
relation!(AndElements, 3);
relation!(LessThanU8Elements, 3);
relation!(RangeCheckU8Elements, 2);

#[cfg(test)]
mod tests {
    use constraints::BytesEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::executor::record::ExecutionTrace;

    use super::*;

    #[test_log::test]
    fn test_range_table() {
        // generate record with byte events
        let span = span!(Level::INFO, "Bytes: Generating Execution Record").entered();
        let mut record = ExecutionTrace::new();
        let n = 1 << 15;
        let mut rng = rand::thread_rng();
        for _ in 0..n {
            let a = rng.gen_range(0..256);
            let b = rng.gen_range(0..256);
            record.add_and_u8_event(a, b);
            if a != b {
                let (min, max) = if a < b { (a, b) } else { (b, a) };
                record.add_less_than_u8_event(min, max);
            }
            record.add_range_check_u8_event(a, b);
        }
        span.exit();
        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let and_elements = AndElements::draw(&mut channel);
        let less_than_u8_elements = LessThanU8Elements::draw(&mut channel);
        let range_check_u8_elements = RangeCheckU8Elements::draw(&mut channel);

        // Trace Generation
        let span = span!(Level::INFO, "Bytes: Trace Generation").entered();
        let constant_trace = preprocessed_trace();
        let (trace, claim) = trace(record.byte_operations.clone());
        let (interaction_trace, interaction_claim) = interaction_trace(
            record.byte_operations,
            &and_elements,
            &less_than_u8_elements,
            &range_check_u8_elements,
        );
        span.exit();

        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component = BytesEval {
            and_elements,
            less_than_u8_elements,
            range_check_u8_elements,
            claim,
        };

        // panics if the constraints are not satisfied
        let _span = span!(Level::INFO, "Bytes: Constraint Assertion").entered();
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(LOG_SIZE),
            |eval| {
                component.evaluate(eval);
            },
            interaction_claim.claimed_sum,
        )
    }
}

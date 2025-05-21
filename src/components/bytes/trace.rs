use super::{
    ByteOperations, BytesPreProcessedColumn, LessThanU8Elements, RangeCheckU8Elements,
    ELEMENT_BITS, LOG_SIZE, N_PREPROCESSED_COLUMNS,
};
use crate::components::{Claim, InteractionClaim};
use std::{array, simd::u32x16};
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, preprocessed_columns::IsFirst, Relation},
    core::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::PackedSecureField,
            SimdBackend,
        },
        fields::m31::{BaseField, M31},
        poly::{
            circle::{CanonicCoset, CircleEvaluation},
            BitReversedOrder,
        },
        ColumnVec,
    },
};
use tracing::{span, Level};

/// Preprocessed Trace for the Bytes Component
/// Rows in the Preprocessed Trace correspond to 0..2^LOG_SIZE values
/// Columns in the Preprocessed Trace correspond to:
/// - a: higher bits
/// - b: lower bits
/// - c_less_than: a < b
/// - is_first: is the first column
pub fn preprocessed_trace() -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>
{
    let _span = span!(Level::INFO, "Bytes: Preprocessed Trace").entered();
    // The Trace is populated
    // The Trace is filled for a, b, c_and, c_less_than and later is_first is added
    let mut trace =
        unsafe { ComponentTrace::<{ N_PREPROCESSED_COLUMNS - 1 }>::uninitialized(LOG_SIZE) };

    // values from 0 to 2^LOG_SIZE
    let values: Vec<_> = (0..(1 << LOG_SIZE)).collect();
    trace
        .iter_mut()
        .zip(values.chunks_exact(N_LANES))
        .for_each(|(mut row, input)| {
            // a: higher bits
            *row[BytesPreProcessedColumn::A as usize] =
                PackedBaseField::from_array(array::from_fn(|i| {
                    M31((input[i] >> ELEMENT_BITS) as u32)
                }));

            // b: lower bits
            *row[BytesPreProcessedColumn::B as usize] =
                PackedBaseField::from_array(array::from_fn(|i| {
                    M31((input[i] & ((1 << ELEMENT_BITS) - 1)) as u32)
                }));

            // c_less_than: a < b
            *row[BytesPreProcessedColumn::CLessThanU8 as usize] =
                PackedBaseField::from_array(array::from_fn(|i| {
                    M31(
                        ((input[i] >> ELEMENT_BITS) < (input[i] & ((1 << ELEMENT_BITS) - 1)))
                            as u32,
                    )
                }));
        });
    let mut constant_trace = trace.to_evals().to_vec();
    constant_trace.push(IsFirst::new(LOG_SIZE).gen_column_simd());
    constant_trace
}

/// Trace for the Byte Operations consist of the multiplicities at the BytesPreProcessedColumn of
/// each specific byte operation.
pub fn trace(
    byte_operations: ByteOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<BytesPreProcessedColumn>,
) {
    let _span = span!(Level::INFO, "Bytes: Main Trace").entered();
    (
        byte_operations
            .into_iter()
            .map(|mult| CircleEvaluation::new(CanonicCoset::new(LOG_SIZE).circle_domain(), mult))
            .collect(),
        Claim::new(LOG_SIZE),
    )
}

/// Interaction Trace for the Byte Events For Logup Constraints
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    less_than_u8_elements: &LessThanU8Elements,
    range_check_u8_elements: &RangeCheckU8Elements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<BytesPreProcessedColumn>,
) {
    let _span = span!(Level::INFO, "Bytes: Interaction Trace").entered();
    let mut logup_gen = LogupTraceGenerator::new(LOG_SIZE);
    let offsets = u32x16::from_array(std::array::from_fn(|i| i as u32));

    // PreCompute a and b elements.
    let total_vec_rows = 1 << (LOG_SIZE - LOG_N_LANES);
    let (a_elems, b_elem_bases): (Vec<_>, Vec<_>) = (0..total_vec_rows)
        .map(|vec_row| {
            let a_elem = vec_row >> (ELEMENT_BITS - LOG_N_LANES);
            let b_elem_base = (vec_row & ((1 << (ELEMENT_BITS - LOG_N_LANES)) - 1)) << LOG_N_LANES;
            (a_elem, b_elem_base)
        })
        .unzip(); // <-- Parallel iterators could speed this up if safe

    // Interaction Trace For Less Than U8 Elements
    // The Relation Elements consists of [a, b, c_less_than]
    // Interaction Trace for Range Check U8 Elements
    // The Relation Elements consists a pair of U8 elements [a, b]
    let mut col_gen = logup_gen.new_col();
    for (vec_row, (&a_elem, &b_elem_base)) in a_elems.iter().zip(&b_elem_bases).enumerate() {
        let a = u32x16::splat(a_elem);
        let b = u32x16::splat(b_elem_base) | offsets;
        let c_less_than = u32x16::from_array(std::array::from_fn(|i| {
            (a_elem < (b_elem_base | i as u32)) as u32
        }));

        // Batch 2 Logup Columns, (Less Than U8 and Range Check U8)
        // sum = (-less_than_mult/less_than_u8_elements) + (-range_check_mult/range_check_u8_elements)
        // sum = -(less_than_mult * range_check_u8_elements + range_check_mult * less_than_u8_elements) / (less_than_u8_elements * range_check_u8_elements)
        // Mult is in Negative as this component is "yielding" values which are "used" by other components
        // a, b, c are in range of 0..256 so we can safely convert them to PackedSecureField from u32x16
        let less_than_elements: PackedSecureField = less_than_u8_elements.combine(
            &[a, b, c_less_than].map(|x| unsafe { PackedBaseField::from_simd_unchecked(x) }),
        );
        let range_check_elements: PackedSecureField = range_check_u8_elements
            .combine(&[a, b].map(|x| unsafe { PackedBaseField::from_simd_unchecked(x) }));

        let less_than_mult = PackedSecureField::from(trace[0].data[vec_row]);
        let range_check_mult = PackedSecureField::from(trace[1].data[vec_row]);
        let denom = less_than_elements * range_check_elements;
        let num = -(less_than_mult * range_check_elements + range_check_mult * less_than_elements);
        col_gen.write_frac(vec_row, num, denom);
    }
    col_gen.finalize_col();

    let (trace, total_sum) = logup_gen.finalize_last();
    let claim = InteractionClaim::new(total_sum);
    (trace, claim)
}

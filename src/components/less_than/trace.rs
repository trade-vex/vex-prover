use crate::{
    components::{bytes::LessThanU8Elements, Claim, InteractionClaim, TraceSize},
    types::N_U64_LIMBS,
};
use itertools::{chain, Itertools};
use num_traits::Zero;
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use std::array;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, preprocessed_columns::IsFirst, Relation},
    core::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::PackedSecureField,
            SimdBackend,
        },
        fields::m31::BaseField,
        poly::{circle::CircleEvaluation, BitReversedOrder},
        ColumnVec,
    },
};
use tracing::{debug, span, Level};

use super::{LessThanColumn, LessThanOperations};

pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Trace for the Less Than Operations, each row consisting of a LessThanOp
pub fn trace(
    mut less_than_operations: LessThanOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<LessThanColumn>,
) {
    let _span = span!(Level::INFO, "Less Than: Main Trace").entered();
    // calculate shape of the trace table
    let log_size = (less_than_operations.len() - 1).ilog2() + 1;
    debug!("Log Size: {}", log_size);
    // pad less_than_operations to a power of 2
    let mut dummy = less_than_operations[0];
    dummy[LessThanColumn::IS_REAL] = BaseField::zero();
    for _ in 0..(1 << log_size) - less_than_operations.len() {
        // adding the first op as dummy op for padding
        less_than_operations.push(dummy);
    }
    let mut trace = ComponentTrace::<{ LessThanColumn::MAIN_COLS }>::zeroed(log_size);
    // Each row of the trace is a LessThanOp field elements arranged as per the `LessThanColumn`
    trace
        .par_iter_mut()
        .zip(
            less_than_operations
                .into_par_iter()
                .chunks(N_LANES)
                .into_par_iter(),
        )
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]); // Extracts the i-th column from 16 rows
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

// Interaction Trace, "use" the LessThanU8Elements for comparison_bytes
// and "yield" to both LessThanElements and StrictLessThanElements based on is_strict
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    less_than_u8_elements: &LessThanU8Elements,
    less_than_elements: &impl Relation<PackedBaseField, PackedSecureField>,
    strict_less_than_elements: &impl Relation<PackedBaseField, PackedSecureField>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<LessThanColumn>,
) {
    let _span = span!(Level::INFO, "Less Than: Interaction Trace").entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let a_col: [&Vec<PackedBaseField>; N_U64_LIMBS] =
        array::from_fn(|i| &trace[LessThanColumn::A + i].data);
    let b_col: [&Vec<PackedBaseField>; N_U64_LIMBS] =
        array::from_fn(|i| &trace[LessThanColumn::B + i].data);
    let c_col = &trace[LessThanColumn::C].data;
    let a_comparison_byte_col = &trace[LessThanColumn::A_COMPARISON_BYTE].data;
    let b_comparison_byte_col = &trace[LessThanColumn::B_COMPARISON_BYTE].data;
    let is_strict_col = &trace[LessThanColumn::IS_STRICT].data;
    let is_real_col = &trace[LessThanColumn::IS_REAL].data;

    // First column: less_than_u8_elements (use)
    let mut col_gen_0 = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let a_comparison_byte = a_comparison_byte_col[vec_row];
        let b_comparison_byte = b_comparison_byte_col[vec_row];
        let is_strict = is_strict_col[vec_row];
        let c_raw = c_col[vec_row];

        // For LessThanU8: c_for_u8 = is_strict * c + (1 - is_strict) * (a_comp != b_comp) * c
        let c_for_u8 = PackedBaseField::from_array({
            let is_strict_arr = is_strict.to_array();
            let a_comp = a_comparison_byte.to_array();
            let b_comp = b_comparison_byte.to_array();
            let c_arr = c_raw.to_array();
            array::from_fn(|i| {
                if is_strict_arr[i] == BaseField::from(1) {
                    c_arr[i]
                } else if a_comp[i] == b_comp[i] {
                    BaseField::zero()
                } else {
                    c_arr[i]
                }
            })
        });

        let values0 = [a_comparison_byte, b_comparison_byte, c_for_u8];
        let p0: PackedSecureField = less_than_u8_elements.combine(&values0);
        col_gen_0.write_frac(vec_row, is_real_col[vec_row].into(), p0);
    }
    col_gen_0.finalize_col();

    // Second column: both less_than_elements and strict_less_than_elements (yields, batched)
    let mut col_gen_1 = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let a: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| a_col[i][vec_row]);
        let b: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| b_col[i][vec_row]);
        let c = c_col[vec_row];
        let is_strict = is_strict_col[vec_row];
        let is_real = is_real_col[vec_row];

        let values = chain!(a.into_iter(), b.into_iter(), std::iter::once(c)).collect_vec();
        let p_strict: PackedSecureField = strict_less_than_elements.combine(&values);
        let p_less_than: PackedSecureField = less_than_elements.combine(&values);

        // Yield to strict_less_than_elements with multiplicity -is_real * is_strict
        // Yield to less_than_elements with multiplicity -is_real * (1 - is_strict)
        let mult_strict = is_real * is_strict;
        let one = PackedBaseField::broadcast(BaseField::from(1));
        let mult_less_than = is_real * (one - is_strict);

        // Convert multiplicities to SecureField for write_frac
        let mult_strict_sf: PackedSecureField = mult_strict.into();
        let mult_less_than_sf: PackedSecureField = mult_less_than.into();

        col_gen_1.write_frac(
            vec_row,
            -(p_strict * mult_less_than_sf + p_less_than * mult_strict_sf),
            p_strict * p_less_than,
        );
    }
    col_gen_1.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

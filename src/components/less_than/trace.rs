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
pub fn trace_eval<const STRICT: bool>(
    mut less_than_operations: LessThanOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<LessThanColumn>,
) {
    let _span = span!(Level::INFO, "Less Than: Main Trace", "Strict {}", STRICT).entered();
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
// and "yield" the LessThanElements for the actual comparison results
pub fn interaction_trace_eval<
    const STRICT: bool,
    R: Relation<PackedBaseField, PackedSecureField>,
>(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    less_than_u8_elements: &LessThanU8Elements,
    less_than_elements: &R,
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
    let is_real_col = &trace[LessThanColumn::IS_REAL].data;

    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let a_comparison_byte = a_comparison_byte_col[vec_row];
        let b_comparison_byte = b_comparison_byte_col[vec_row];
        let a: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| a_col[i][vec_row]);
        let b: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| b_col[i][vec_row]);
        let mut c = c_col[vec_row];
        // LessThanElements Values, The Component using the value can ensure that a < b is c.
        let values1 = chain!(a.into_iter(), b.into_iter(), std::iter::once(c)).collect_vec();

        if !STRICT {
            // this can be avoided by adding a strict and less than col in the preprocessed trace
            // the result of c "used" in the less_than_u8_elements returns 0 when a_comparison_byte = b_comparison_byte
            c = PackedBaseField::from_array({
                let a_comp = a_comparison_byte.to_array();
                let b_comp = b_comparison_byte.to_array();
                let c = c_col[vec_row].to_array();
                array::from_fn(|i| {
                    if a_comp[i] == b_comp[i] {
                        BaseField::zero()
                    } else {
                        c[i]
                    }
                })
            });
        }

        // LessThanU8Elements Values, LookUp ensures that result is a_comparison_byte < b_comparison_byte is c.
        let values0 = [a_comparison_byte, b_comparison_byte, c];
        let p1: PackedSecureField = less_than_u8_elements.combine(&values0);
        let p2: PackedSecureField = less_than_elements.combine(&values1);
        // 1/p1 - 1/p2 is the claimed sum for the row
        col_gen.write_frac(vec_row, (p2 - p1) * is_real_col[vec_row], p1 * p2);
    }
    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

use super::{AddColumn, AddElements, AddOperations};
use crate::components::bytes::RangeCheckU8Elements;
use crate::{
    components::{Claim, InteractionClaim, TraceSize},
    types::N_U64_LIMBS,
};

use num_traits::{One, Zero};
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

/// Generates the preprocessed trace with an "IsFirst" column.
/// Ensures that the trace size is a power of 2.
pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Generates the main trace for addition operations.
/// Each row represents an `AddOp` and follows the `AddColumn` structure.
pub fn trace(
    mut add_operations: AddOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<AddColumn>,
) {
    let _span = span!(Level::INFO, "Add: Main Trace").entered();

    // Calculate the log size, ensuring the trace size is a power of 2
    let log_size = (add_operations.len() - 1).ilog2() + 1;
    debug!("Log Size: {}", log_size);

    // Pad operations to ensure a power of 2 trace size
    for _ in 0..(1 << log_size) - add_operations.len() {
        add_operations.push([BaseField::zero(); AddColumn::MAIN_COLS]);
    }
    let mut trace = ComponentTrace::<{ AddColumn::MAIN_COLS }>::zeroed(log_size);

    // Populate the trace using SIMD for parallel processing.`
    trace
        .par_iter_mut()
        .zip(
            add_operations
                .into_par_iter()
                .chunks(N_LANES) // Process in chunks of N_LANES (SIMD width)
                .into_par_iter(),
        )
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]);
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    // Convert trace to evaluations and create a claim
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

/// Generates the interaction trace.
/// - Uses `AddU8Elements` for byte-wise addition checks.
/// - Uses `AddElements` to store final addition results.
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    range_check_u8_elements: &RangeCheckU8Elements,
    add_elements: &AddElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<AddColumn>,
) {
    let _span = span!(Level::INFO, "Add: Interaction Trace").entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let values: [&Vec<PackedBaseField>; 3 * N_U64_LIMBS] =
        array::from_fn(|i| &trace[AddColumn::A + i].data);
    let is_real_col = &trace[AddColumn::IS_REAL].data;

    // Process each byte-pair in groups of 4, applying range checks.
    for i in (0..24).step_by(4) {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let a0 = values[i][vec_row];
            let a1 = values[i + 1][vec_row];
            let a2 = values[i + 2][vec_row];
            let a3 = values[i + 3][vec_row];
            let p0: PackedSecureField = range_check_u8_elements.combine(&[a0, a1]);
            let p1: PackedSecureField = range_check_u8_elements.combine(&[a2, a3]);
            col_gen.write_frac(vec_row, (p0 + p1) * is_real_col[vec_row], p0 * p1);
        }
        col_gen.finalize_col();
    }

    // Process the final interaction trace with the addition elements.
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values: [PackedBaseField; 3 * N_U64_LIMBS] = array::from_fn(|i| values[i][vec_row]);
        let p: PackedSecureField = add_elements.combine(&values);
        col_gen.write_frac(vec_row, -PackedSecureField::one() * is_real_col[vec_row], p);
    }
    col_gen.finalize_col();
    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

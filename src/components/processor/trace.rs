use crate::{
    components::{
        trace_utils::{add_interaction_col, add_interaction_col_batched},
        Claim, InteractionClaim, TraceSize,
    },
    executor::{
        instruction::{InstructionColumn, InstructionElements},
        record::Instructions,
        state::{StateElements, N_STATE_FELTS},
    },
};
use itertools::Itertools;
use num_traits::{One, Zero};
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSlice,
};
use std::array;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use crate::components::IsFirst;
use stwo_constraint_framework::LogupTraceGenerator;
use stwo_prover::{
    core::{fields::m31::BaseField, poly::circle::CanonicCoset, ColumnVec},
    prover::{
        backend::simd::{
            m31::{PackedBaseField, N_LANES},
            qm31::PackedSecureField,
            SimdBackend,
        },
        poly::{circle::CircleEvaluation, BitReversedOrder},
    },
};
use tracing::{debug, span, Level};

use super::ProcessorColumn;

/// Preprocessed Trace for Processor Trace, each row consisting of a single field element
/// First row is M31(1), rest are M31(0)
pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Trace for the Processor Component
/// The Trace must consist of all the instructions on both IMT's
/// each row consisting of a [BaseField; InstructionColumn::MAIN_COLS]
pub fn trace(
    mut instructions: Instructions<BaseField>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<ProcessorColumn>,
) {
    let _span = span!(Level::INFO, "Processor: Main Trace").entered();
    // calculate shape of the trace table
    let log_size = (instructions.len() - 1).ilog2() + 1;
    debug!("Log Size: {}", log_size);
    // pad instructions to a power of 2
    let mut dummy = instructions[0];
    dummy[InstructionColumn::IS_REAL] = BaseField::zero();
    for _ in 0..(1 << log_size) - instructions.len() {
        instructions.push(dummy);
    }
    let mut trace = ComponentTrace::<{ ProcessorColumn::MAIN_COLS }>::zeroed(log_size);
    trace
        .par_iter_mut()
        .zip(instructions.par_chunks_exact(N_LANES))
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]); // Extracts the i-th column from 16 rows
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

/// Processor Interaction Trace
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    state_elements: &StateElements,
    instruction_elements: &InstructionElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<ProcessorColumn>,
) {
    let _span = span!(Level::INFO, "Processor: Interaction Trace").entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let initial_state: [&Vec<PackedBaseField>; N_STATE_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::INITIAL_STATE + i].data);
    let is_real = &trace[InstructionColumn::IS_REAL].data;
    let final_state: [&Vec<PackedBaseField>; N_STATE_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::FINAL_STATE + i].data);
    let instruction = trace.iter().map(|c| &c.data).collect_vec();

    // 1st interaction column
    // batched interaction columns for initial and final state
    add_interaction_col_batched(
        &mut logup_gen,
        &initial_state,
        &final_state,
        is_real,
        log_size,
        state_elements,
        PackedSecureField::one(),
        -PackedSecureField::one(),
    );

    // 2nd interaction column
    // interaction column for instruction elements
    add_interaction_col(
        &mut logup_gen,
        &instruction,
        is_real,
        log_size,
        instruction_elements,
        PackedSecureField::one(),
    );
    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

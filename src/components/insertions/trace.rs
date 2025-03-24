use crate::{
    components::{
        less_than::{LessThanElements, StrictLessThanElements},
        poseidon::PoseidonElements,
        trace_utils::{
            add_interaction_col, add_less_than_interaction_col, add_merkle_interaction_col,
        },
        Claim, InteractionClaim, TraceSize,
    },
    executor::{flatten_single, instruction::InstructionColumn, instruction::InstructionElements},
    flatten,
    hash::{N_ELEMENTS, N_HASH, N_STATE},
    imt::{
        leaf::LeafColumn, side::OrderSide, side::Side, MERKLE_HEIGHT, N_LEAF_FELTS, N_U64_FELTS,
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
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, preprocessed_columns::IsFirst},
    core::{
        backend::{
            simd::{
                column::BaseColumn,
                m31::{PackedBaseField, N_LANES},
                qm31::PackedSecureField,
                SimdBackend,
            },
            Column,
        },
        fields::m31::BaseField,
        poly::{circle::CircleEvaluation, BitReversedOrder},
        ColumnVec,
    },
};
use tracing::{debug, span, Level};

use super::{Insertions, InsertionsColumn};

/// Preprocessed Trace for Insertions, each row consisting of a single field element
/// First row is M31(1), rest are M31(0)
pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Trace for the Insertion Operations, each row consisting of a [BaseField; InstructionColumn::MAIN_COLS]
pub fn trace<S: OrderSide>(
    mut insertions: Insertions,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<InsertionsColumn>,
) {
    let _span = span!(Level::INFO, "Insertions: Main Trace", "{}", S::NAME).entered();
    // calculate shape of the trace table
    let log_size = (insertions.len() - 1).ilog2() + 1;
    debug!("Log Size: {}", log_size);
    // pad insertions to a power of 2
    let mut dummy = insertions[0];
    dummy[InstructionColumn::IS_REAL] = BaseField::zero();
    for _ in 0..(1 << log_size) - insertions.len() {
        insertions.push(dummy);
    }
    let mut trace = ComponentTrace::<{ InsertionsColumn::MAIN_COLS }>::zeroed(log_size);
    trace
        .par_iter_mut()
        .zip(insertions.par_chunks_exact(N_LANES))
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]); // Extracts the i-th column from 16 rows
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

/// Insertions Interaction Trace
pub fn interaction_trace<S: OrderSide>(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_elements: &PoseidonElements,
    less_than_elements: &LessThanElements,
    strict_less_than_elements: &StrictLessThanElements,
    instruction_elements: &InstructionElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<InsertionsColumn>,
) {
    let _span = span!(Level::INFO, "Insertions: Interaction Trace", "{}", S::NAME).entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let low_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_LEAF + i].data);
    let low_merkle_proof: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT] = array::from_fn(|i| {
        array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PROOF + i * N_HASH + j].data)
    });
    let low_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PATH + i * N_HASH + j].data)
        });
    let updated_low_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| {
                &trace[InstructionColumn::UPDATED_LOW_MERKLE_PATH + i * N_HASH + j].data
            })
        });
    let low_index: [&Vec<PackedBaseField>; MERKLE_HEIGHT] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_INDEX + i].data);
    let leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LEAF + i].data);
    let merkle_proof: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT] = array::from_fn(|i| {
        array::from_fn(|j| &trace[InstructionColumn::MERKLE_PROOF + i * N_HASH + j].data)
    });
    let merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] = array::from_fn(|i| {
        array::from_fn(|j| &trace[InstructionColumn::MERKLE_PATH + i * N_HASH + j].data)
    });
    let updated_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::UPDATED_MERKLE_PATH + i * N_HASH + j].data)
        });
    let index: [&Vec<PackedBaseField>; MERKLE_HEIGHT] =
        array::from_fn(|i| &trace[InstructionColumn::INDEX + i].data);

    let mut updated_low_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] = low_leaf.clone();
    updated_low_leaf[LeafColumn::NEXT..N_LEAF_FELTS]
        .copy_from_slice(&leaf[LeafColumn::LABEL..LeafColumn::NEXT]);

    let is_real = &trace[InstructionColumn::IS_REAL].data;

    let inactive_leaf_data = BaseColumn::zeros(1 << log_size).data;
    let inactive_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|_| &inactive_leaf_data);

    let low_price: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| low_leaf[LeafColumn::PRICE + i]);
    let low_time: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| low_leaf[LeafColumn::TIME + i]);
    let inserted_price: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| leaf[LeafColumn::PRICE + i]);
    let inserted_time: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| leaf[LeafColumn::TIME + i]);
    let next_price: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| low_leaf[LeafColumn::NEXT_PRICE + i]);
    let next_time: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| low_leaf[LeafColumn::NEXT_TIME + i]);

    // Constraint 3 in constraints.rs
    // low_time < inserted_time
    add_less_than_interaction_col(
        &mut logup_gen,
        &low_time,
        &inserted_time,
        is_real,
        log_size,
        strict_less_than_elements,
    );

    // Constraint 3 in constraints.rs
    // next_time < inserted_time
    add_less_than_interaction_col(
        &mut logup_gen,
        &next_time,
        &inserted_time,
        is_real,
        log_size,
        strict_less_than_elements,
    );

    // Constraint 4 in constraints.rs
    match S::side() {
        Side::Buy => {
            // inserted_price <= low_price
            add_less_than_interaction_col(
                &mut logup_gen,
                &inserted_price,
                &low_price,
                is_real,
                log_size,
                less_than_elements,
            );
            // next_price < inserted_price
            add_less_than_interaction_col(
                &mut logup_gen,
                &next_price,
                &inserted_price,
                is_real,
                log_size,
                strict_less_than_elements,
            );
        }
        Side::Sell => {
            // low_price <= inserted_price
            add_less_than_interaction_col(
                &mut logup_gen,
                &low_price,
                &inserted_price,
                is_real,
                log_size,
                less_than_elements,
            );
            // inserted_price < next_price
            add_less_than_interaction_col(
                &mut logup_gen,
                &inserted_price,
                &next_price,
                is_real,
                log_size,
                strict_less_than_elements,
            );
        }
    }

    // A Total of 2 leaf updates are performed
    // for each update
    //   - Verify the Merkle Prooof, leaf hash + Merkle Proof -> Merkle Path
    //   - Update the leaf, merkle path ==> updated merkle path, proof remains the same
    for (index, leaf, updated_leaf, proof, path, updated_path) in [
        (
            low_index,
            low_leaf,
            updated_low_leaf,
            low_merkle_proof,
            low_merkle_path,
            updated_low_merkle_path,
        ),
        (
            index,
            inactive_leaf,
            leaf,
            merkle_proof,
            merkle_path,
            updated_merkle_path,
        ),
    ] {
        for (leaf, proof, path) in [(leaf, proof, path), (updated_leaf, proof, updated_path)].iter()
        {
            let leaf_state: [&Vec<PackedBaseField>; N_STATE] = leaf[0..N_STATE].try_into().unwrap();
            let leaf_hash = path[0];
            let elements: [&Vec<PackedBaseField>; N_ELEMENTS] = flatten!(leaf_state, leaf_hash);
            // add the leaf hash interaction
            add_interaction_col(
                &mut logup_gen,
                &elements,
                is_real,
                log_size,
                poseidon_elements,
                PackedSecureField::one(),
            );
            let mut curr = leaf_hash;
            // add the merkle path interaction
            for (i, (sibling, hash)) in proof.iter().zip(path.iter().skip(1)).enumerate() {
                add_merkle_interaction_col(
                    &mut logup_gen,
                    &curr,
                    sibling,
                    hash,
                    index[i],
                    is_real,
                    log_size,
                    poseidon_elements,
                );
                curr = hash.clone();
            }
        }
    }
    let values = trace.iter().map(|c| &c.data).collect_vec();
    // add the instruction interaction, that yields the final state
    add_interaction_col(
        &mut logup_gen,
        &values,
        is_real,
        log_size,
        instruction_elements,
        -PackedSecureField::one(),
    );
    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

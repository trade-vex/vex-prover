use crate::{
    components::{
        addition::AddElements,
        less_than::LessThanElements,
        order_match::MatchElements,
        poseidon::PoseidonElements,
        trace_utils::{
            add_interaction_col, add_leaf_interaction_col_batched, add_less_than_interaction_col,
            add_merkle_interaction_col_batched, MerkleStep,
        },
        Claim, InteractionClaim,
    },
    executor::{
        flatten_single,
        instruction::{InstructionColumn, InstructionElements, N_INSTRUCTION_FELTS},
        record::Instructions,
        state::StateColumn,
    },
    flatten,
    hash::{N_ELEMENTS, N_HASH, N_STATE},
    imt::{
        leaf::{Leaf, LeafColumn},
        side::{MatchType, OrderMatchType, OrderSide, Side},
        MERKLE_HEIGHT, N_LEAF_FELTS, N_U64_FELTS,
    },
};
use itertools::{chain, Itertools};
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
        backend::{
            simd::{
                column::BaseColumn,
                m31::{PackedBaseField, LOG_N_LANES, N_LANES},
                qm31::PackedSecureField,
                SimdBackend,
            },
            Column,
        },
        poly::{circle::CircleEvaluation, BitReversedOrder},
    },
};
use tracing::{debug, span, Level};

use super::PartialMatchColumn;

/// Preprocessed Trace for Partial Order Matches, each row consisting of a single field element
/// First row is M31(1), rest are M31(0)
pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Trace for the Order Match Operations, each row consisting of a [BaseField; InstructionColumn::MAIN_COLS]
/// Generic over the Order Side and Order Match Type
/// This Function does not check the validity of the instructions
pub fn trace<S: OrderSide, T: OrderMatchType>(
    mut partial_matches: Instructions<BaseField>,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<PartialMatchColumn<T>>,
) {
    let _span = span!(
        Level::INFO,
        "Partial Matches: Main Trace",
        "{} {}",
        T::NAME,
        S::NAME,
    )
    .entered();
    // calculate shape of the trace table
    let log_size = (partial_matches.len() - 1).ilog2() + 1;
    debug!("Len: {}", partial_matches.len());
    debug!("Log Size: {}", log_size);
    // pad partial_matches to a power of 2
    let mut dummy = partial_matches[0];
    dummy[InstructionColumn::IS_REAL] = BaseField::zero();
    for _ in 0..(1 << log_size) - partial_matches.len() {
        partial_matches.push(dummy);
    }
    let mut trace = ComponentTrace::<N_INSTRUCTION_FELTS>::zeroed(log_size);
    trace
        .par_iter_mut()
        .zip(partial_matches.par_chunks_exact(N_LANES))
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]); // Extracts the i-th column from 16 rows
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

/// Partial Order Match Interaction Trace
/// Generic over the Order Side and Order Match Type
/// Note: The trace must consist the same type of instructions as the generic
/// This Function does not check the validity of the instructions
pub fn interaction_trace<S: OrderSide, T: OrderMatchType>(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_elements: &PoseidonElements,
    less_than_elements: &LessThanElements,
    instruction_elements: &InstructionElements,
    match_elements: &MatchElements,
    add_elements: &AddElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<PartialMatchColumn<T>>,
) {
    let _span = span!(
        Level::INFO,
        "Partial Matches: Interaction Trace",
        "{} {}",
        T::NAME,
        S::NAME,
    )
    .entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LEAF + i].data);

    let low_leaf_data = BaseColumn::zeros(1 << log_size).data;
    let mut low_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] = array::from_fn(|_| &low_leaf_data);
    let active = vec![PackedBaseField::one(); 1 << (log_size - LOG_N_LANES)];
    low_leaf[LeafColumn::ACTIVE] = &active;
    let low_price_time_cols = Leaf::<BaseField, S>::first_price_time_cols(log_size);
    for (i, col) in low_price_time_cols.iter().enumerate() {
        low_leaf[LeafColumn::LABEL + i] = col;
    }
    for (i, col) in leaf[LeafColumn::LABEL..LeafColumn::NEXT].iter().enumerate() {
        low_leaf[LeafColumn::NEXT + i] = col;
    }

    let filled_volume: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_LEAF + i].data);
    let remaining_volume: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_LEAF + N_U64_FELTS + i].data);
    let total_volume: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LEAF + LeafColumn::VOLUME + i].data);
    let mut updated_leaf = leaf;
    for i in 0..N_U64_FELTS {
        updated_leaf[LeafColumn::VOLUME + i] = remaining_volume[i];
    }

    let low_merkle_proof: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT] = array::from_fn(|i| {
        array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PROOF + i * N_HASH + j].data)
    });
    let low_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PATH + i * N_HASH + j].data)
        });
    let low_index: [&Vec<PackedBaseField>; MERKLE_HEIGHT] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_INDEX + i].data);
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

    let is_real = &trace[InstructionColumn::IS_REAL].data;

    let price: [&Vec<PackedBaseField>; N_U64_FELTS] =
        array::from_fn(|i| leaf[LeafColumn::PRICE + i]);
    match T::MATCHTYPE {
        MatchType::Aggressive => {
            let trade_price = match S::SIDE {
                Side::Buy => {
                    let trade_price: [&Vec<PackedBaseField>; N_U64_FELTS] = array::from_fn(|i| {
                        &trace[InstructionColumn::INITIAL_STATE + StateColumn::BEST_SELL_PRICE + i]
                            .data
                    });
                    add_less_than_interaction_col(
                        &mut logup_gen,
                        &trade_price,
                        &price,
                        is_real,
                        log_size,
                        less_than_elements,
                    );
                    trade_price
                }
                Side::Sell => {
                    let trade_price: [&Vec<PackedBaseField>; N_U64_FELTS] = array::from_fn(|i| {
                        &trace[InstructionColumn::INITIAL_STATE + StateColumn::BEST_BUY_PRICE + i]
                            .data
                    });
                    add_less_than_interaction_col(
                        &mut logup_gen,
                        &price,
                        &trade_price,
                        is_real,
                        log_size,
                        less_than_elements,
                    );
                    trade_price
                }
            };
            add_interaction_col(
                &mut logup_gen,
                &chain!(trade_price.into_iter(), filled_volume.into_iter()).collect_vec(),
                is_real,
                log_size,
                match_elements,
                -PackedSecureField::one(),
            );
        }
        MatchType::Passive => {
            add_interaction_col(
                &mut logup_gen,
                &chain!(price.into_iter(), filled_volume.into_iter()).collect_vec(),
                is_real,
                log_size,
                match_elements,
                PackedSecureField::one(),
            );
        }
    }

    add_interaction_col(
        &mut logup_gen,
        &chain!(
            filled_volume.into_iter(),
            remaining_volume.into_iter(),
            total_volume.into_iter()
        )
        .collect_vec(),
        is_real,
        log_size,
        add_elements,
        PackedSecureField::one(),
    );

    // A Total of 3 merkle proofs (partial match doesn't update low leaf):
    //   1. Low leaf - original path
    //   2. Matched leaf - original path
    //   3. Matched leaf - updated path (marked inactive)
    //
    // Batching strategy:
    //   - Batch all 3 leaf hashes into 1 column
    //   - Batch all 3 merkle steps at each level into 1 column per level (20 columns total)

    // Batch all 3 leaf hash operations together
    let leaf_batch = vec![
        // Proof 1: Low leaf - original
        {
            let leaf_state: [&Vec<PackedBaseField>; N_STATE] =
                low_leaf[0..N_STATE].try_into().unwrap();
            let leaf_hash = low_merkle_path[0];
            let elements_array: [&Vec<PackedBaseField>; N_ELEMENTS] =
                flatten!(leaf_state, leaf_hash);
            let elements = elements_array.to_vec();
            (elements, PackedSecureField::one())
        },
        // Proof 2: Matched leaf - original
        {
            let leaf_state: [&Vec<PackedBaseField>; N_STATE] = leaf[0..N_STATE].try_into().unwrap();
            let leaf_hash = merkle_path[0];
            let elements_array: [&Vec<PackedBaseField>; N_ELEMENTS] =
                flatten!(leaf_state, leaf_hash);
            let elements = elements_array.to_vec();
            (elements, PackedSecureField::one())
        },
        // Proof 3: Matched leaf - updated (inactive)
        {
            let leaf_state: [&Vec<PackedBaseField>; N_STATE] =
                updated_leaf[0..N_STATE].try_into().unwrap();
            let leaf_hash = updated_merkle_path[0];
            let elements_array: [&Vec<PackedBaseField>; N_ELEMENTS] =
                flatten!(leaf_state, leaf_hash);
            let elements = elements_array.to_vec();
            (elements, PackedSecureField::one())
        },
    ];

    add_leaf_interaction_col_batched(
        &mut logup_gen,
        &[leaf_batch],
        is_real,
        log_size,
        poseidon_elements,
    );

    // Batch Merkle steps by level: for each level, batch all 3 proofs' steps together
    let mut merkle_batches: Vec<Vec<MerkleStep>> = Vec::with_capacity(MERKLE_HEIGHT);

    for level in 0..MERKLE_HEIGHT {
        let mut level_batch = Vec::with_capacity(3);

        // Proof 1: Low leaf - original path
        level_batch.push(MerkleStep {
            curr: low_merkle_path[level].to_vec(),
            sibling: low_merkle_proof[level].to_vec(),
            hash: low_merkle_path[level + 1].to_vec(),
            index_bit: low_index[level],
            mult: PackedSecureField::one(),
        });

        // Proof 2: Matched leaf - original path
        level_batch.push(MerkleStep {
            curr: merkle_path[level].to_vec(),
            sibling: merkle_proof[level].to_vec(),
            hash: merkle_path[level + 1].to_vec(),
            index_bit: index[level],
            mult: PackedSecureField::one(),
        });

        // Proof 3: Matched leaf - updated path
        level_batch.push(MerkleStep {
            curr: updated_merkle_path[level].to_vec(),
            sibling: merkle_proof[level].to_vec(),
            hash: updated_merkle_path[level + 1].to_vec(),
            index_bit: index[level],
            mult: PackedSecureField::one(),
        });

        merkle_batches.push(level_batch);
    }

    add_merkle_interaction_col_batched(
        &mut logup_gen,
        &merkle_batches,
        is_real,
        log_size,
        poseidon_elements,
    );

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

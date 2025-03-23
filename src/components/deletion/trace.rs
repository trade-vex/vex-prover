use crate::components::poseidon::PoseidonElements;
use crate::executor::flatten_single;
use crate::executor::instruction::InstructionElements;
use crate::hash::N_ELEMENTS;
use crate::imt::leaf::LeafColumn;

use crate::imt::N_U64_FELTS;
use crate::{
    components::{Claim, InteractionClaim, TraceSize},
    executor::instruction::InstructionColumn,
    flatten,
    hash::{N_HASH, N_STATE},
    imt::{side::OrderSide, MERKLE_HEIGHT, N_LEAF_FELTS},
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
    constraint_framework::{logup::LogupTraceGenerator, preprocessed_columns::IsFirst, Relation},
    core::{
        backend::{
            simd::{
                column::BaseColumn,
                m31::{PackedBaseField, LOG_N_LANES, N_LANES},
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

use super::{Deletions, DeletionsColumn};

//Preprocessed Trace for Deletion, each row consisting of a single field element
/// First row is M31(1), rest are M31(0)
pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

pub fn trace<S: OrderSide>(
    mut deletions: Deletions,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<DeletionsColumn>,
) {
    let _span = span!(Level::INFO, "Deletions: Main Trace", "{}", S::NAME).entered();
    // calculate shape of the trace table
    println!("deletions length {}", deletions.len());
    
    // debug!("Log Size: {}", log_size);
    // println!("Log Size: {}", log_size);
    println!("LOG_N_LANES: {}", LOG_N_LANES);
    // pad deletions to a power of 2
    let mut dummy = deletions[0];
    dummy[InstructionColumn::IS_REAL] = BaseField::zero();
    while deletions.len() < 16 {
        println!("hello");
        deletions.push(deletions[0]);
    }
    let mut log_size = (deletions.len() - 1).ilog2() + 1;
    println!("log size2 {}", log_size);
    println!("deletions length2 {}", deletions.len());
    let mut trace = ComponentTrace::<{ DeletionsColumn::MAIN_COLS }>::zeroed(log_size);
    trace
        .par_iter_mut()
        .zip(deletions.par_chunks_exact(N_LANES))
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]); // Extracts the i-th column from 16 rows
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

/// Deletions Interaction Trace
pub fn interaction_trace<S: OrderSide>(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_elements: &PoseidonElements,
    instruction_elements: &InstructionElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<DeletionsColumn>,
) {
    let _span = span!(Level::INFO, "Deletions: Interaction Trace", "{}", S::NAME).entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let prev_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_LEAF + i].data);
    let prev_merkle_proof: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT] = array::from_fn(|i| {
        array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PROOF + i * N_HASH + j].data)
    });
    let prev_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::LOW_MERKLE_PATH + i * N_HASH + j].data)
        });
    let updated_prev_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| {
                &trace[InstructionColumn::UPDATED_LOW_MERKLE_PATH + i * N_HASH + j].data
            })
        });
    let prev_index: [&Vec<PackedBaseField>; MERKLE_HEIGHT] =
        array::from_fn(|i| &trace[InstructionColumn::LOW_INDEX + i].data);
    let target_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] =
        array::from_fn(|i| &trace[InstructionColumn::LEAF + i].data);
    let target_merkle_proof: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::MERKLE_PROOF + i * N_HASH + j].data)
        });
    let target_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::MERKLE_PATH + i * N_HASH + j].data)
        });
    let updated_target_merkle_path: [[&Vec<PackedBaseField>; N_HASH]; MERKLE_HEIGHT + 1] =
        array::from_fn(|i| {
            array::from_fn(|j| &trace[InstructionColumn::UPDATED_MERKLE_PATH + i * N_HASH + j].data)
        });
    let target_index: [&Vec<PackedBaseField>; MERKLE_HEIGHT] =
        array::from_fn(|i| &trace[InstructionColumn::INDEX + i].data);

    let mut updated_prev_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] = prev_leaf.clone();
    // Update prev leaf's next pointer to target leaf's next pointer
    updated_prev_leaf[LeafColumn::NEXT..LeafColumn::NEXT + 2 * N_U64_FELTS]
        .copy_from_slice(&target_leaf[LeafColumn::NEXT..LeafColumn::NEXT + 2 * N_U64_FELTS]);

    let is_real = &trace[InstructionColumn::IS_REAL].data;

    let empty_leaf_data = BaseColumn::zeros(1 << log_size).data;
    let empty_leaf: [&Vec<PackedBaseField>; N_LEAF_FELTS] = array::from_fn(|_| &empty_leaf_data);

    // A Total of 4 leaf updates are performed
    // for each update
    //   - Verify the Merkle Proof, leaf hash + Merkle Proof -> Merkle Path
    //   - Update the leaf, merkle path ==> updated merkle path, proof remains the same
    for (index, leaf, updated_leaf, proof, path, updated_path) in [
        (
            prev_index,
            prev_leaf,
            updated_prev_leaf,
            prev_merkle_proof,
            prev_merkle_path,
            updated_prev_merkle_path,
        ),
        (
            target_index,
            target_leaf,
            empty_leaf,
            target_merkle_proof,
            target_merkle_path,
            updated_target_merkle_path,
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

/// add_interaction_col adds an interaction column to the logup generator for the given lookup elements in the given columns
fn add_interaction_col<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    cols: &[&Vec<PackedBaseField>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &X,
    mult: PackedSecureField,
) {
    let mut col_gen = logup_gen.new_col();
    println!("cols length1 {}", cols.len());
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values1: Vec<PackedBaseField> = cols.iter().map(|col| col[vec_row]).collect();
        let p1 = lookup_elements.combine(&values1);
        col_gen.write_frac(vec_row, mult * is_real[vec_row], p1);
    }
    println!("cols length2 {}", cols.len());
    col_gen.finalize_col();
}

/// add_merkle_interaction_col adds an interaction column to the logup generator for the current and sibling columns
/// the left and right values are determined by the index column
/// [left, right, hash] -> lookup_elements
fn add_merkle_interaction_col<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    curr: &[&Vec<PackedBaseField>],
    sibling: &[&Vec<PackedBaseField>],
    hash: &[&Vec<PackedBaseField>],
    index: &Vec<PackedBaseField>,
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &X,
) {
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let cur: Vec<PackedBaseField> = curr.iter().map(|col| col[vec_row]).collect();
        let sib: Vec<PackedBaseField> = sibling.iter().map(|col| col[vec_row]).collect();
        let hash: Vec<PackedBaseField> = hash.iter().map(|col| col[vec_row]).collect();
        let index: PackedBaseField = index[vec_row];
        let (mut left, right): (Vec<PackedBaseField>, Vec<PackedBaseField>) = cur
            .into_iter()
            .zip(sib.into_iter())
            .map(|(a, b)| {
                let a = a.to_array();
                let b = b.to_array();
                let index = index.to_array();
                let mut left = [BaseField::zero(); N_LANES];
                let mut right = [BaseField::zero(); N_LANES];
                for i in 0..N_LANES {
                    if index[i] == BaseField::zero() {
                        left[i] = a[i];
                        right[i] = b[i];
                    } else {
                        left[i] = b[i];
                        right[i] = a[i];
                    }
                }
                (
                    PackedBaseField::from_array(left),
                    PackedBaseField::from_array(right),
                )
            })
            .unzip();
        left.extend(right);
        left.extend(hash);
        let p1 = lookup_elements.combine(&left);
        col_gen.write_frac(vec_row, PackedSecureField::one() * is_real[vec_row], p1);
    }
    col_gen.finalize_col();
}

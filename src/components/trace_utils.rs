use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, Relation},
    core::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::PackedSecureField,
        },
        fields::m31::BaseField,
    },
};

/// add_interaction_col adds an interaction column to the logup generator for the given lookup elements in the given columns
pub fn add_interaction_col<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    cols: &[&Vec<PackedBaseField>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &X,
    mult: PackedSecureField,
) {
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values1: Vec<PackedBaseField> = cols.iter().map(|col| col[vec_row]).collect();
        let p1 = lookup_elements.combine(&values1);
        col_gen.write_frac(vec_row, mult * is_real[vec_row], p1);
    }
    col_gen.finalize_col();
}

/// add_less_than_interaction_col adds an interaction column to the logup generator for the given a and b columns
/// for strict less than comparison lookup elements must be StrictLessThanElements
/// for less than comparison lookup elements must be LessThanElements
pub fn add_less_than_interaction_col<R: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    col_a: &[&Vec<PackedBaseField>],
    col_b: &[&Vec<PackedBaseField>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &R,
) {
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let a: Vec<PackedBaseField> = col_a.iter().map(|col| col[vec_row]).collect();
        let b: Vec<PackedBaseField> = col_b.iter().map(|col| col[vec_row]).collect();
        let c = PackedBaseField::one();
        let values = chain!(a.into_iter(), b.into_iter(), std::iter::once(c)).collect_vec();
        let p1 = lookup_elements.combine(&values);
        col_gen.write_frac(vec_row, PackedSecureField::one() * is_real[vec_row], p1);
    }
    col_gen.finalize_col();
}

/// add_merkle_interaction_col adds an interaction column to the logup generator for the current and sibling columns
/// the left and right values are determined by the index column
/// [left, right, hash] -> lookup_elements
pub fn add_merkle_interaction_col<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    curr: &[&Vec<PackedBaseField>],
    sibling: &[&Vec<PackedBaseField>],
    hash: &[&Vec<PackedBaseField>],
    index: &Vec<PackedBaseField>,
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &X,
    mult: PackedSecureField,
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
        col_gen.write_frac(vec_row, mult * is_real[vec_row], p1);
    }
    col_gen.finalize_col();
}

/// add_interaction_col adds an interaction column to the logup generator for the given lookup elements in the given columns
pub fn add_interaction_col_batched<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    cols1: &[&Vec<PackedBaseField>],
    cols2: &[&Vec<PackedBaseField>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    lookup_elements: &X,
    mult1: PackedSecureField,
    mult2: PackedSecureField,
) {
    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let values1: Vec<PackedBaseField> = cols1.iter().map(|col| col[vec_row]).collect();
        let values2: Vec<PackedBaseField> = cols2.iter().map(|col| col[vec_row]).collect();
        let p1 = lookup_elements.combine(&values1);
        let p2 = lookup_elements.combine(&values2);
        col_gen.write_frac(
            vec_row,
            (p2 * mult1 + p1 * mult2) * is_real[vec_row],
            p1 * p2,
        );
    }
    col_gen.finalize_col();
}

use itertools::{chain, Itertools};
use num_traits::{One, Zero};
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

/// generate preprocessed column for is_first
/// is_first is a column that is 1 for the first row and 0 for the rest
pub fn is_first(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// add_interaction_col adds an interaction column to the logup generator for the given lookup elements in the given columns
pub fn add_interaction_col<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    cols: &[&Vec<PackedBaseField>],
    is_real: &[PackedBaseField],
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
    is_real: &[PackedBaseField],
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
    index: &[PackedBaseField],
    is_real: &[PackedBaseField],
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
    is_real: &[PackedBaseField],
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

/// Descriptor for a single Merkle verification step
/// Used for batching multiple Merkle steps into a single interaction column
#[derive(Clone)]
pub struct MerkleStep<'a> {
    pub curr: Vec<&'a Vec<PackedBaseField>>,
    pub sibling: Vec<&'a Vec<PackedBaseField>>,
    pub hash: Vec<&'a Vec<PackedBaseField>>,
    pub index_bit: &'a Vec<PackedBaseField>,
    pub mult: PackedSecureField,
}

/// Batch multiple Merkle verification steps into a single interaction column
/// This reduces the number of columns from N steps to N/4 columns (batches of 4)
/// Uses common denominator technique: (a/b + c/d) = (ad + bc)/(bd)
pub fn add_merkle_interaction_col_batched<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    batches: &[Vec<MerkleStep>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    poseidon_elements: &X,
) {
    for batch in batches {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerator = PackedSecureField::zero();
            let mut denominator = PackedSecureField::one();

            for step in batch {
                // Extract values for this Merkle step
                let curr: Vec<PackedBaseField> = step.curr.iter().map(|col| col[vec_row]).collect();
                let sibling: Vec<PackedBaseField> = step.sibling.iter().map(|col| col[vec_row]).collect();
                let hash: Vec<PackedBaseField> = step.hash.iter().map(|col| col[vec_row]).collect();
                let index_bit = step.index_bit[vec_row];

                // Compute left/right based on index bit
                let (mut left, right): (Vec<PackedBaseField>, Vec<PackedBaseField>) = curr
                    .into_iter()
                    .zip(sibling.into_iter())
                    .map(|(a, b)| {
                        let a_arr = a.to_array();
                        let b_arr = b.to_array();
                        let index_arr = index_bit.to_array();
                        let mut left = [BaseField::zero(); N_LANES];
                        let mut right = [BaseField::zero(); N_LANES];
                        for i in 0..N_LANES {
                            if index_arr[i] == BaseField::zero() {
                                left[i] = a_arr[i];
                                right[i] = b_arr[i];
                            } else {
                                left[i] = b_arr[i];
                                right[i] = a_arr[i];
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

                // Combine into Poseidon lookup
                let frac_denom = poseidon_elements.combine(&left);

                // Accumulate using common denominator: (a/b + c/d) = (a*d + c*b)/(b*d)
                // old_sum = numerator / denominator
                // new_fraction = mult / frac_denom
                // new_sum = (numerator * frac_denom + mult * denominator) / (denominator * frac_denom)
                numerator = numerator * frac_denom.clone() + step.mult * denominator.clone();
                denominator *= frac_denom;
            }

            col_gen.write_frac(vec_row, numerator * is_real[vec_row], denominator);
        }
        col_gen.finalize_col();
    }
}

/// Batch multiple leaf hash interactions into a single column
/// Similar to add_merkle_interaction_col_batched but for leaf hashes
pub fn add_leaf_interaction_col_batched<X: Relation<PackedBaseField, PackedSecureField>>(
    logup_gen: &mut LogupTraceGenerator,
    batches: &[Vec<(Vec<&Vec<PackedBaseField>>, PackedSecureField)>],
    is_real: &Vec<PackedBaseField>,
    log_size: u32,
    poseidon_elements: &X,
) {
    for batch in batches {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerator = PackedSecureField::zero();
            let mut denominator = PackedSecureField::one();

            for (cols, mult) in batch {
                let values: Vec<PackedBaseField> = cols.iter().map(|col| col[vec_row]).collect();
                let frac_denom = poseidon_elements.combine(&values);

                // Accumulate using common denominator: (a/b + c/d) = (a*d + c*b)/(b*d)
                numerator = numerator * frac_denom.clone() + *mult * denominator.clone();
                denominator *= frac_denom;
            }

            col_gen.write_frac(vec_row, numerator * is_real[vec_row], denominator);
        }
        col_gen.finalize_col();
    }
}

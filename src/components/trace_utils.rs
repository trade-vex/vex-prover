use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use stwo_constraint_framework::{LogupTraceGenerator, Relation};
use stwo_prover::{
    core::{fields::m31::BaseField, poly::circle::CanonicCoset, ColumnVec},
    prover::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::PackedSecureField,
            SimdBackend,
        },
        backend::{Col, Column},
        poly::{circle::CircleEvaluation, BitReversedOrder},
    },
};

// IsFirst: A column with `1` at the first position, and `0` elsewhere.
// Copied from stwo examples since it's not exported from the main crate
pub struct IsFirst {
    log_size: u32,
}

impl IsFirst {
    pub const fn new(log_size: u32) -> Self {
        Self { log_size }
    }

    pub fn gen_column_simd(&self) -> CircleEvaluation<SimdBackend, BaseField, BitReversedOrder> {
        let mut col = Col::<SimdBackend, BaseField>::zeros(1 << self.log_size);
        col.set(0, BaseField::one());
        CircleEvaluation::new(CanonicCoset::new(self.log_size).circle_domain(), col)
    }
}

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
    use crate::hash::{N_HASH, N_ELEMENTS};

    for batch in batches {
        let mut col_gen = logup_gen.new_col();
        // Pre-allocate reusable buffers to avoid allocations in inner loops
        let mut poseidon_values = Vec::with_capacity(N_ELEMENTS);
        let mut reordered = Vec::with_capacity(N_ELEMENTS);

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerator = PackedSecureField::zero();
            let mut denominator = PackedSecureField::one();

            for step in batch {
                poseidon_values.clear();
                reordered.clear();

                let index_bit = step.index_bit[vec_row];
                let index_arr = index_bit.to_array();

                // Compute left/right and collect directly into poseidon_values
                // Avoiding intermediate Vec allocations
                for i in 0..N_HASH {
                    let curr_val = step.curr[i][vec_row];
                    let sibling_val = step.sibling[i][vec_row];

                    let curr_arr = curr_val.to_array();
                    let sibling_arr = sibling_val.to_array();

                    let mut left = [BaseField::zero(); N_LANES];
                    let mut right = [BaseField::zero(); N_LANES];

                    for lane in 0..N_LANES {
                        if index_arr[lane] == BaseField::zero() {
                            left[lane] = curr_arr[lane];
                            right[lane] = sibling_arr[lane];
                        } else {
                            left[lane] = sibling_arr[lane];
                            right[lane] = curr_arr[lane];
                        }
                    }

                    poseidon_values.push(PackedBaseField::from_array(left));
                    // Store right values temporarily - we'll add them after the loop
                    poseidon_values.push(PackedBaseField::from_array(right));
                }

                // Now rearrange: we want all left values, then all right values, then hash
                // Currently we have: [left0, right0, left1, right1, ...]
                // We need: [left0, left1, ..., right0, right1, ..., hash0, hash1, ...]

                // Add left values (even indices)
                for i in (0..2*N_HASH).step_by(2) {
                    reordered.push(poseidon_values[i]);
                }

                // Add right values (odd indices)
                for i in (1..2*N_HASH).step_by(2) {
                    reordered.push(poseidon_values[i]);
                }

                // Add hash values
                for i in 0..N_HASH {
                    reordered.push(step.hash[i][vec_row]);
                }

                // Combine into Poseidon lookup
                let frac_denom = poseidon_elements.combine(&reordered);

                // Accumulate using common denominator: (a/b + c/d) = (a*d + c*b)/(b*d)
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
    use crate::hash::N_ELEMENTS;

    for batch in batches {
        let mut col_gen = logup_gen.new_col();
        // Pre-allocate reusable buffer to avoid allocations in inner loop
        let mut values = Vec::with_capacity(N_ELEMENTS);

        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            let mut numerator = PackedSecureField::zero();
            let mut denominator = PackedSecureField::one();

            for (cols, mult) in batch {
                values.clear();
                // Reuse the buffer instead of creating a new Vec each iteration
                for col in cols {
                    values.push(col[vec_row]);
                }
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

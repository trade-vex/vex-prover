use std::array;

use num_traits::identities::*;
use stwo_prover::core::fields::m31::BaseField;

pub const EXTERNAL_ROUND_CONSTS: [[BaseField; N_STATE]; 2 * N_HALF_FULL_ROUNDS] =
    [[BaseField::from_u32_unchecked(1234); N_STATE]; 2 * N_HALF_FULL_ROUNDS];
pub const INTERNAL_ROUND_CONSTS: [BaseField; N_PARTIAL_ROUNDS] =
    [BaseField::from_u32_unchecked(1234); N_PARTIAL_ROUNDS];
pub const N_PARTIAL_ROUNDS: usize = 14;
pub const N_HALF_FULL_ROUNDS: usize = 4;
pub const N_STATE: usize = 16;

pub fn permutation(mut state: [BaseField; N_STATE]) -> [BaseField; N_STATE] {
    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] += EXTERNAL_ROUND_CONSTS[round][i];
        });
        apply_external_round_matrix(&mut state);
        state = std::array::from_fn(|i| pow5(state[i]));
    });

    // Partial rounds.
    (0..N_PARTIAL_ROUNDS).for_each(|round| {
        state[0] += BaseField::from(INTERNAL_ROUND_CONSTS[round]);
        apply_internal_round_matrix(&mut state);
        state[0] = pow5(state[0]);
    });

    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] += BaseField::from(EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i]);
        });
        apply_external_round_matrix(&mut state);
        state = std::array::from_fn(|i| pow5(state[i]));
    });
    state
}

pub fn hash_leaf(input: [BaseField; 16]) -> [BaseField; 8] {
    let result: [BaseField; 16] = permutation(input);
    let mut output = array::from_fn(|_| BaseField::zero());
    output[..8].copy_from_slice(&result[..8]);
    output
}

pub fn compress(input: &[&[BaseField; 8]; 2]) -> [BaseField; 8] {
    // Combine the two slices into a single array of length 16
    let mut combined = [BaseField::zero(); 16];
    combined[..8].copy_from_slice(&input[0][..]);
    combined[8..].copy_from_slice(&input[1][..]);

    // Apply the permutation function to the combined array
    let permuted = permutation(combined);

    // Return the first 8 elements of the permuted array as the result
    let mut output = [BaseField::zero(); 8];
    output.copy_from_slice(&permuted[..8]);
    output
}

/// Applies the external round matrix.
/// See <https://eprint.iacr.org/2023/323.pdf> 5.1 and Appendix B.
pub fn apply_external_round_matrix(state: &mut [BaseField; 16]) {
    // Applies circ(2M4, M4, M4, M4).
    for i in 0..4 {
        [
            state[4 * i],
            state[4 * i + 1],
            state[4 * i + 2],
            state[4 * i + 3],
        ] = apply_m4([
            state[4 * i],
            state[4 * i + 1],
            state[4 * i + 2],
            state[4 * i + 3],
        ]);
    }
    for j in 0..4 {
        let s = state[j] + state[j + 4] + state[j + 8] + state[j + 12];
        for i in 0..4 {
            state[4 * i + j] += s;
        }
    }
}

// Applies the internal round matrix.
//   mu_i = 2^{i+1} + 1.
// See <https://eprint.iacr.org/2023/323.pdf> 5.2.
pub fn apply_internal_round_matrix(state: &mut [BaseField; 16]) {
    // TODO(shahars): Check that these coefficients are good according to section  5.3 of Poseidon2
    // paper.
    let sum = state[1..].iter().fold(state[0], |acc, s| acc + *s);
    state.iter_mut().enumerate().for_each(|(i, s)| {
        // TODO(andrew): Change to rotations.
        *s = *s * BaseField::from_u32_unchecked(1 << (i + 1)) + sum;
    });
}

pub fn pow5(x: BaseField) -> BaseField {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x
}

#[inline(always)]
/// Applies the M4 MDS matrix described in <https://eprint.iacr.org/2023/323.pdf> 5.1.
fn apply_m4(x: [BaseField; 4]) -> [BaseField; 4] {
    let t0 = x[0] + x[1];
    let t02 = t0 + t0;
    let t1 = x[2] + x[3];
    let t12 = t1 + t1;
    let t2 = x[1] + x[1] + t1;
    let t3 = x[3] + x[3] + t0;
    let t4 = t12 + t12 + t3;
    let t5 = t02 + t02 + t2;
    let t6 = t3 + t5;
    let t7 = t2 + t4;
    [t6, t5, t7, t4]
}

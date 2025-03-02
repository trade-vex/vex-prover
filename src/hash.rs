//! # Attribution
//! This code is based on the implementation from the StarksWare's STWO repository.
//! The original code can be found [here](https://github.com/starkware-libs/stwo/blob/dev/crates/prover/src/examples/poseidon/mod.rs)

use std::array;

use crate::constants::{EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, MAT_DIAG16_M_1};
use num_traits::identities::*;
use stwo_prover::core::fields::m31::BaseField;

pub const N_PARTIAL_ROUNDS: usize = 14;
pub const N_HALF_FULL_ROUNDS: usize = 4;
pub const N_STATE: usize = 16;

pub fn permutation(state: &mut [BaseField; N_STATE]) {
    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] += EXTERNAL_ROUND_CONSTS[round][i];
        });
        apply_external_round_matrix(state);
        *state = std::array::from_fn(|i| pow5(state[i]));
    });

    // Partial rounds.
    (0..N_PARTIAL_ROUNDS).for_each(|round| {
        state[0] += BaseField::from(INTERNAL_ROUND_CONSTS[round]);
        apply_internal_round_matrix(state);
        state[0] = pow5(state[0]);
    });

    // 4 full rounds.
    (0..N_HALF_FULL_ROUNDS).for_each(|round| {
        (0..N_STATE).for_each(|i| {
            state[i] += BaseField::from(EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i]);
        });
        apply_external_round_matrix(state);
        *state = std::array::from_fn(|i| pow5(state[i]));
    });
}

pub fn hash_leaf(mut state: [BaseField; 16]) -> [BaseField; 8] {
    permutation(&mut state);
    let mut output = array::from_fn(|_| BaseField::zero());
    output[..8].copy_from_slice(&state[..8]);
    output
}

pub fn compress(input: &[&[BaseField; 8]; 2]) -> [BaseField; 8] {
    // Combine the two slices into a single array of length 16(initial state)
    let mut combined = [BaseField::zero(); 16];
    combined[..8].copy_from_slice(&input[0][..]);
    combined[8..].copy_from_slice(&input[1][..]);

    // Apply the permutation function to the combined array
    permutation(&mut combined);

    // The first 8 elements as hash of the permuted array are returned as the result
    let mut output = [BaseField::zero(); 8];
    output.copy_from_slice(&combined[..8]);
    output
}

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

pub fn apply_internal_round_matrix(state: &mut [BaseField; 16]) {
    let sum = state[1..].iter().fold(state[0], |acc, s| acc + *s);
    state.iter_mut().enumerate().for_each(|(i, s)| {
        (*s) = (*s) * MAT_DIAG16_M_1[i] + sum;
    });
}

pub fn pow5(x: BaseField) -> BaseField {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x
}

#[inline(always)]
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

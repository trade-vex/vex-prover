//! # Attribution
//! This code is based on the implementation from the StarksWare's STWO repository.
//! The original code can be found [here](https://github.com/starkware-libs/stwo/blob/dev/crates/prover/src/examples/poseidon/mod.rs)

use std::{
    array,
    ops::{Add, AddAssign, Mul, Sub},
};

use crate::constants::{EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS, MAT_DIAG16_M_1};
use num_traits::identities::*;
use stwo_prover::core::fields::{m31::BaseField, FieldExpOps};

pub const N_PARTIAL_ROUNDS: usize = 14;
pub const N_HALF_FULL_ROUNDS: usize = 4;
pub const N_FULL_ROUNDS: usize = 2 * N_HALF_FULL_ROUNDS;
pub const N_STATE: usize = 16;
pub const N_HASH: usize = 8;
pub const N_ELEMENTS: usize = N_STATE + N_HASH;

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

pub fn apply_external_round_matrix<F>(state: &mut [F; 16])
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    // Applies circ(2M4, M4, M4, M4).
    for i in 0..4 {
        [
            state[4 * i],
            state[4 * i + 1],
            state[4 * i + 2],
            state[4 * i + 3],
        ] = apply_m4([
            state[4 * i].clone(),
            state[4 * i + 1].clone(),
            state[4 * i + 2].clone(),
            state[4 * i + 3].clone(),
        ]);
    }
    for j in 0..4 {
        let s =
            state[j].clone() + state[j + 4].clone() + state[j + 8].clone() + state[j + 12].clone();
        for i in 0..4 {
            state[4 * i + j] += s.clone();
        }
    }
}

pub fn apply_internal_round_matrix<F>(state: &mut [F; 16])
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    let sum = state[1..]
        .iter()
        .cloned()
        .fold(state[0].clone(), |acc, s| acc + s);
    state.iter_mut().enumerate().for_each(|(i, s)| {
        (*s) = s.clone() * MAT_DIAG16_M_1[i] + sum.clone();
    });
}

pub fn pow5<F: FieldExpOps>(x: F) -> F {
    let x2 = x.clone() * x.clone();
    let x4 = x2.clone() * x2.clone();
    x4 * x.clone()
}

#[inline(always)]
pub fn apply_m4<F>(x: [F; 4]) -> [F; 4]
where
    F: Clone + AddAssign<F> + Add<F, Output = F> + Sub<F, Output = F> + Mul<BaseField, Output = F>,
{
    let t0 = x[0].clone() + x[1].clone();
    let t02 = t0.clone() + t0.clone();
    let t1 = x[2].clone() + x[3].clone();
    let t12 = t1.clone() + t1.clone();
    let t2 = x[1].clone() + x[1].clone() + t1.clone();
    let t3 = x[3].clone() + x[3].clone() + t0.clone();
    let t4 = t12.clone() + t12.clone() + t3.clone();
    let t5 = t02.clone() + t02.clone() + t2.clone();
    let t6 = t3.clone() + t5.clone();
    let t7 = t2.clone() + t4.clone();
    [t6, t5, t7, t4]
}

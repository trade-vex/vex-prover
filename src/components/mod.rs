use std::{marker::PhantomData, vec};
use stwo_prover::core::{
    channel::Channel,
    fields::{qm31::SecureField, secure_column::SECURE_EXTENSION_DEGREE},
    pcs::TreeVec,
};
pub mod addition;
pub mod bytes;
pub mod less_than;

/// Const trait that defines the number of columns in the trace table
pub trait TraceSize {
    /// Number of columns in the main trace table
    const MAIN_COLS: usize;
    /// Number of columns in the interaction trace table
    const INTERACTION_COLS: usize;

    // Compile-time validation
    const ASSERT: () = assert!(Self::MAIN_COLS > 0 && Self::INTERACTION_COLS > 0);
}

/// Generic Claim to implement for claims each component
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Claim<T: TraceSize> {
    pub log_size: u32,
    _marker: PhantomData<T>,
}

impl<T: TraceSize> Claim<T> {
    pub const fn new(log_size: u32) -> Self {
        _ = T::ASSERT;

        Self {
            log_size,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub const fn main_cols() -> usize {
        T::MAIN_COLS
    }

    #[inline(always)]
    pub const fn interaction_cols() -> usize {
        T::INTERACTION_COLS
    }

    #[inline]
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![
            vec![self.log_size],
            vec![self.log_size; T::MAIN_COLS],
            vec![self.log_size; SECURE_EXTENSION_DEGREE * T::INTERACTION_COLS],
        ])
    }

    #[inline(always)]
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(u64::from(self.log_size));
    }
}

/// Generic InteractionClaim to implement for interaction claims each component

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct InteractionClaim<T: TraceSize> {
    pub claimed_sum: SecureField,
    _marker: PhantomData<T>,
}

impl<T: TraceSize> InteractionClaim<T> {
    pub const fn new(claimed_sum: SecureField) -> Self {
        let _ = T::ASSERT;

        Self {
            claimed_sum,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

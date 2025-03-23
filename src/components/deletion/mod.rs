use super::TraceSize;
use crate::{executor::instruction::N_INSTRUCTION_FELTS, imt::MERKLE_HEIGHT};
use stwo_prover::core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE};

mod constraints;
mod trace;

pub use trace::{interaction_trace, preprocessed_trace, trace};

pub type Deletions = Vec<[BaseField; DeletionsColumn::MAIN_COLS]>;

#[derive(Debug, Clone)]
pub struct DeletionsColumn;

impl TraceSize for DeletionsColumn {
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    /// number of poseidon hashes: 4 times for leaf hashes
    ///     - 1 for target_merkle_proof
    ///     - 1 for parent_merkle_proof
    ///     - 1 for updated parent_leaf
    ///     - 1 for empty leaf
    ///  4*MERKLE_HEIGHT for merkle paths verification
    /// Total Poseidon Interactions: 4 + 4*MERKLE_HEIGHT
    /// Target and parent time checks => 1 equality check
    /// Target and parent price checks => 1 equality check
    /// Total Equality Interactions: 2
    /// 1 column for yielding the final result
    /// Total Columns: 4 + 4*MERKLE_HEIGHT + 2 + 1  = 4*MERKLE_HEIGHT + 9
    const INTERACTION_COLS: usize = (4 * MERKLE_HEIGHT + 5) * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {}

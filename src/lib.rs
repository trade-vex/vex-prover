#![feature(btree_cursors, portable_simd, iter_array_chunks)]

use components::{bytes::BytesPreProcessedColumn, Claim, InteractionClaim};
use stwo_prover::core::{prover::StarkProof, vcs::ops::MerkleHasher};
pub mod components;
pub mod constants;
pub mod error;
pub mod executor;
pub mod hash;
pub mod imt;
pub mod types;

pub struct VexProof<H: MerkleHasher> {
    pub stark_proof: StarkProof<H>,
    pub claim: VexClaim,
    pub interaction_claim: VexInteractionClaim,
}

pub struct VexClaim {
    /// The public inputs to the circuit.
    pub inputs: Vec<u8>,
    /// public outputs contains the root hash of the IMT
    pub outputs: Vec<u8>,
    /// bytes component claim
    pub bytes_claim: Claim<BytesPreProcessedColumn>,
    // followed by claims for each component
}

pub struct VexInteractionClaim {
    /// Bytes component interaction claim
    pub bytes_interaction_claim: InteractionClaim<BytesPreProcessedColumn>,
}
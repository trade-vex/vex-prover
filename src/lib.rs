#![feature(btree_cursors)]

use stwo_prover::core::{prover::StarkProof, vcs::ops::MerkleHasher};
pub mod components;
pub mod constants;
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
    // followed by claims for each component
}

pub struct VexInteractionClaim {}

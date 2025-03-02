use crate::imt::{leaf::Leaf, MerklePath, MerkleProof};

/// Instruction represents a single instruction in the program
/// Represents an instruction with its opcode, Merkle proof, and Merkle path.
/// Every Row in the main trace corresponds to an instruction
#[derive(Clone, Copy)]
pub struct Instruction<F> {
    /// The opcode of the instruction
    pub opcode: Opcode,
    /// Low Leafs Merkle Proof to which the instruction applies
    /// Merkle Proof contains sibling hashes of the leafs in the path from the leaf to the root
    pub low_merkle_proof: MerkleProof<F>,
    /// Low Leafs Merkle Path to which the instruction applies
    /// Merkle Path containts the hash of the leafs in the path from the leaf to the root
    pub low_merkle_path: MerklePath<F>,
    /// Updated Low Leafs Merkle Path after the instruction is applied
    pub updated_low_merkle_path: MerklePath<F>,
    /// Low Leafs Index in the IMT
    pub low_index: F,
    /// Low Leaf
    pub low_leaf: Leaf<F>,
    /// Merkle Proof of the leaf to which the instruction applies
    pub merkle_proof: MerkleProof<F>,
    /// Merkle Path of the leaf to which the instruction applies
    pub merkle_path: MerklePath<F>,
    /// Updated Merkle Path after the instruction is applied
    pub updated_merkle_path: MerklePath<F>,
    /// Index of the leaf in the IMT
    pub index: F,
    /// Leaf to which the instruction applies
    pub leaf: Leaf<F>,
}

#[derive(Clone, Copy)]
pub enum Opcode {
    PlaceBuyOrder,
    PlaceSellOrder,
    UpdateBuyOrder,
    UpdateSellOrder,
    CancelBuyOrder,
    CancelSellOrder,
    ExecuteBuyOrder,
    ExecuteSellOrder,
    PartialExecuteBuyOrder,
    PartialExecuteSellOrder,
}

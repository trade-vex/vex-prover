use std::array;

use stwo_prover::{constraint_framework::EvalAtRow, core::fields::m31::BaseField, relation};

use crate::{
    hash::N_HASH,
    imt::{IndexBits, LeafFelts, MerklePath, MerkleProof, MERKLE_HEIGHT, N_LEAF_FELTS},
};

use super::state::{State, N_STATE_FELTS};

pub const N_INSTRUCTION_FELTS: usize = InstructionColumn::N_INSTRUCTION_FELTS;

/// Instruction represents a single instruction in the program
/// Represents an instruction with its opcode, Merkle proof, and Merkle path.
/// Every Row in the main trace corresponds to an instruction
#[derive(Clone, Copy, Debug)]
pub struct Instruction<F> {
    /// initial state before the instruction is applied
    pub initial_state: State<F>,
    /// The opcode of the instruction
    pub opcode: F,
    /// Low Leafs Merkle Proof to which the instruction applies
    /// Merkle Proof contains sibling hashes of the leafs in the path from the leaf to the root
    pub low_merkle_proof: MerkleProof<F>,
    /// Low Leafs Merkle Path to which the instruction applies
    /// Merkle Path containts the hash of the leafs in the path from the leaf to the root
    pub low_merkle_path: MerklePath<F>,
    /// Updated Low Leafs Merkle Path after the instruction is applied
    pub updated_low_merkle_path: MerklePath<F>,
    /// Low Leafs Index in the IMT
    pub low_index: IndexBits<F>,
    // @todo:rename this field
    /// Additional Data for Instruction
    /// Insertions: Contains Actual Low Leaf
    /// Updates: First N_U64_FELTS contain new Volume, rest zero
    /// PartialMatch: First N_U64_FELTS contain Filled Volume,
    ///               Next N_U64_FELTS contain Remaining Volume,
    /// this is because we dont need low leaf when verifying constraints
    /// the low leaf can be constructed from side and leaf.
    pub low_leaf: LeafFelts<F>,
    /// Merkle Proof of the leaf to which the instruction applies
    pub merkle_proof: MerkleProof<F>,
    /// Merkle Path of the leaf to which the instruction applies
    pub merkle_path: MerklePath<F>,
    /// Updated Merkle Path after the instruction is applied
    pub updated_merkle_path: MerklePath<F>,
    /// Index of the leaf in the IMT
    pub index: IndexBits<F>,
    /// Leaf to which the instruction applies
    pub leaf: LeafFelts<F>,
    /// final state after the instruction is applied
    pub final_state: State<F>,
    /// is_real flag to check if the operation is not among the dummy padded operations
    pub is_real: F,
}

impl<F> Instruction<F> {
    /// from_eval returns a LessThanOp instance from a given EvalAtRow instance
    pub fn from_eval<E: EvalAtRow>(eval: &mut E) -> Instruction<E::F> {
        let initial_state = State::<E::F>::from_eval(eval);
        let opcode = eval.next_trace_mask();
        let low_merkle_proof = array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let low_merkle_path = array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let updated_low_merkle_path =
            array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let low_index = array::from_fn(|_| eval.next_trace_mask());
        let low_leaf = array::from_fn(|_| eval.next_trace_mask());
        let merkle_proof = array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let merkle_path = array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let updated_merkle_path = array::from_fn(|_| array::from_fn(|_| eval.next_trace_mask()));
        let index = array::from_fn(|_| eval.next_trace_mask());
        let leaf = array::from_fn(|_| eval.next_trace_mask());
        let final_state = State::<E::F>::from_eval(eval);
        let is_real = eval.next_trace_mask();
        Instruction {
            initial_state,
            opcode,
            low_merkle_proof,
            low_merkle_path,
            updated_low_merkle_path,
            low_index,
            low_leaf,
            merkle_proof,
            merkle_path,
            updated_merkle_path,
            index,
            leaf,
            final_state,
            is_real,
        }
    }
}

pub struct InstructionColumn;

impl InstructionColumn {
    pub const INITIAL_STATE: usize = 0;
    pub const OPCODE: usize = Self::INITIAL_STATE + N_STATE_FELTS;
    pub const LOW_MERKLE_PROOF: usize = Self::OPCODE + 1;
    pub const LOW_MERKLE_PATH: usize = Self::LOW_MERKLE_PROOF + MERKLE_HEIGHT * N_HASH;
    pub const UPDATED_LOW_MERKLE_PATH: usize = Self::LOW_MERKLE_PATH + (MERKLE_HEIGHT + 1) * N_HASH;
    pub const LOW_INDEX: usize = Self::UPDATED_LOW_MERKLE_PATH + (MERKLE_HEIGHT + 1) * N_HASH;
    pub const LOW_LEAF: usize = Self::LOW_INDEX + MERKLE_HEIGHT;
    pub const MERKLE_PROOF: usize = Self::LOW_LEAF + N_LEAF_FELTS;
    pub const MERKLE_PATH: usize = Self::MERKLE_PROOF + MERKLE_HEIGHT * N_HASH;
    pub const UPDATED_MERKLE_PATH: usize = Self::MERKLE_PATH + (MERKLE_HEIGHT + 1) * N_HASH;
    pub const INDEX: usize = Self::UPDATED_MERKLE_PATH + (MERKLE_HEIGHT + 1) * N_HASH;
    pub const LEAF: usize = Self::INDEX + MERKLE_HEIGHT;
    pub const FINAL_STATE: usize = Self::LEAF + N_LEAF_FELTS;
    pub const IS_REAL: usize = Self::FINAL_STATE + N_STATE_FELTS;
    pub const N_INSTRUCTION_FELTS: usize = Self::IS_REAL + 1;
}

// InstructionElements are used in the processor component
// and yielded by the specific insutruction's component
// the number of elements used/yielded is equal to the number of columns in the instruction
relation!(InstructionElements, {
    InstructionColumn::N_INSTRUCTION_FELTS
});

/// The Higher Level Operation to be performed in both the IMTs
#[derive(Clone, Copy, Debug)]
pub enum Opcode {
    InsertBuyOrder,
    InsertSellOrder,
    UpdateBuyOrder,
    UpdateSellOrder,
    CancelBuyOrder,
    CancelSellOrder,
    MatchAggressiveBuy,
    MatchPassiveBuy,
    MatchAggressiveSell,
    MatchPassiveSell,
    PartialMatchAggressiveBuy,
    PartialMatchPassiveBuy,
    PartialMatchAggressiveSell,
    PartialMatchPassiveSell,
}

impl Opcode {
    /// from field returns an Opcode instance from a given field
    pub fn from_field(felt: BaseField) -> Opcode {
        match felt.0 {
            0 => Opcode::InsertBuyOrder,
            1 => Opcode::InsertSellOrder,
            2 => Opcode::UpdateBuyOrder,
            3 => Opcode::UpdateSellOrder,
            4 => Opcode::CancelBuyOrder,
            5 => Opcode::CancelSellOrder,
            6 => Opcode::MatchAggressiveBuy,
            7 => Opcode::MatchAggressiveSell,
            8 => Opcode::MatchPassiveBuy,
            9 => Opcode::MatchPassiveSell,
            10 => Opcode::PartialMatchAggressiveBuy,
            11 => Opcode::PartialMatchAggressiveSell,
            12 => Opcode::PartialMatchPassiveBuy,
            13 => Opcode::PartialMatchPassiveSell,
            _ => panic!("Invalid Opcode"),
        }
    }

    /// to_field returns a field instance from a given Opcode
    pub fn to_field(&self) -> BaseField {
        match self {
            Opcode::InsertBuyOrder => BaseField::from_u32_unchecked(0),
            Opcode::InsertSellOrder => BaseField::from_u32_unchecked(1),
            Opcode::UpdateBuyOrder => BaseField::from_u32_unchecked(2),
            Opcode::UpdateSellOrder => BaseField::from_u32_unchecked(3),
            Opcode::CancelBuyOrder => BaseField::from_u32_unchecked(4),
            Opcode::CancelSellOrder => BaseField::from_u32_unchecked(5),
            Opcode::MatchAggressiveBuy => BaseField::from_u32_unchecked(6),
            Opcode::MatchAggressiveSell => BaseField::from_u32_unchecked(7),
            Opcode::MatchPassiveBuy => BaseField::from_u32_unchecked(8),
            Opcode::MatchPassiveSell => BaseField::from_u32_unchecked(9),
            Opcode::PartialMatchAggressiveBuy => BaseField::from_u32_unchecked(10),
            Opcode::PartialMatchAggressiveSell => BaseField::from_u32_unchecked(11),
            Opcode::PartialMatchPassiveBuy => BaseField::from_u32_unchecked(12),
            Opcode::PartialMatchPassiveSell => BaseField::from_u32_unchecked(13),
        }
    }
}

/// 5 Types of IMT Operations
pub enum IMTOperation {
    Insertion,
    Update,
    Deletion,
    MatchAggressive,
    MatchPassive,
    PartialMatchAggressive,
    PartialMatchPassive,
}

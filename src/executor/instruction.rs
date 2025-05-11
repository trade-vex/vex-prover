use std::array;

use stwo_prover::{constraint_framework::EvalAtRow, core::fields::m31::BaseField, relation};

use super::state::{State, N_STATE_FELTS};
use crate::{
    hash::N_HASH,
    imt::{IndexBits, LeafFelts, MerklePath, MerkleProof, MERKLE_HEIGHT, N_LEAF_FELTS},
};
use num_traits::FromPrimitive;

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
#[repr(u32)]
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
    pub fn from_field(f: BaseField) -> Opcode {
        FromPrimitive::from_u32(f.0).expect("invalid opcode")
    }
    pub fn to_field(self) -> BaseField {
        BaseField::from_u32_unchecked(self as u32)
    }
}

impl FromPrimitive for Opcode {
    fn from_u64(num: u64) -> Option<Opcode> {
        match num {
            0 => Some(Opcode::InsertBuyOrder),
            1 => Some(Opcode::InsertSellOrder),
            2 => Some(Opcode::UpdateBuyOrder),
            3 => Some(Opcode::UpdateSellOrder),
            4 => Some(Opcode::CancelBuyOrder),
            5 => Some(Opcode::CancelSellOrder),
            6 => Some(Opcode::MatchAggressiveBuy),
            7 => Some(Opcode::MatchPassiveBuy),
            8 => Some(Opcode::MatchAggressiveSell),
            9 => Some(Opcode::MatchPassiveSell),
            10 => Some(Opcode::PartialMatchAggressiveBuy),
            11 => Some(Opcode::PartialMatchPassiveBuy),
            12 => Some(Opcode::PartialMatchAggressiveSell),
            13 => Some(Opcode::PartialMatchPassiveSell),
            _ => None,
        }
    }

    fn from_i64(num: i64) -> Option<Opcode> {
        Self::from_u64(num as u64)
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

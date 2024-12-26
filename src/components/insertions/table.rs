use crate::types::Hash;
use stwo_prover::core::fields::m31::BaseField;

use crate::imt::MERKLE_HEIGHT;

pub struct InsertionTable {
    table: Vec<InsertionRow>,
}

impl InsertionTable {
    pub fn new() -> Self {
        Self { table: Vec::new() }
    }

    pub fn add_row(&mut self, row: InsertionRow) {
        self.table.push(row);
    }

    pub fn get(&self, index: usize) -> Option<&InsertionRow> {
        self.table.get(index)
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    
}

pub struct InsertionRow {
    /// low leaf - immediate predecessor of the leaf being inserted
    pub low_leaf: [BaseField; 6],
    /// order being inserted ((Price, Time), Volume)
    pub order: ((BaseField, BaseField), BaseField),
    /// low_index - index of the low leaf in the leaves
    pub low_index: BaseField,
    /// low proof - proof of membership of the low leaf
    pub low_merkle_proof: [(Hash<BaseField>, Hash<BaseField>); MERKLE_HEIGHT],
    /// initial root hash
    pub initial_root: [BaseField; 8],
    /// inactive index - index of the next inactive leaf in the leaves
    pub inactive_index: BaseField,
    /// inactivity proof - proof of inactivity where the order is being inserted
    pub inactivity_proof: [(Hash<BaseField>, Hash<BaseField>); MERKLE_HEIGHT],
    /// final root hash after insertion
    pub final_root: [BaseField; 8],
}

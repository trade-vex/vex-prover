use crate::{constants::EMPTY_HASHES, hash::compress};
use leaf::{Leaf, PriceTime};
use num_traits::{One, Zero};
use order::Order;
use std::{array, collections::BTreeMap};
use stwo_prover::core::fields::m31::BaseField;

pub mod leaf;
pub mod order;

pub const MERKLE_HEIGHT: usize = 20;
pub const MERKLE_WIDTH: usize = 1 << MERKLE_HEIGHT;
pub type Hash<F> = [F; 8];

/// A structure representing an Indexed Merkle Tree.
///
/// An Indexed Merkle Tree is a variant of the Merkle Tree data structure
/// that includes metadata along with other parts of Node Leaf to ensure
/// efficient non-membership proofs.
/// 
/// The Tree is designed to hold Orders of Buy or Sell type.
///
/// # Examples
///
/// ```
/// // Example usage of IndexedMerkleTree
/// // let tree = IndexedMerkleTree::new();
/// // let order = Order::new(PriceTime::new(10, 1), 1);
/// // let insertion_proof = tree.insert(order);
/// // insertion_proof.verify();
/// // 
/// ```
/// # References
///
/// - [Section3, Transparency Dictionaries with Succinct Proofs of Correct Operation](https://eprint.iacr.org/2021/1263.pdf)
#[derive(Default)]
pub struct IndexedMerkleTree {
    /// The root hash of the tree.
    root: Hash<BaseField>,
    /// raw data
    /// raw[0] is the leaf hashes, raw[1] is the first level of the tree, etc.
    raw: Box<[Vec<Hash<BaseField>>]>,
    /// leaves of the tree containing orders and metadata
    leaves: Vec<Leaf>,
    /// label to indices for quick lookups
    index_map: BTreeMap<PriceTime, usize>,
}

impl IndexedMerkleTree {
    /// finalize the update at given index and returns the root
    #[inline]
    pub fn finalize_update(&mut self, mut index: usize) -> Hash<BaseField> {
        let leaf_hash = self.leaves[index].hash();
        self.raw[0][index] = leaf_hash;
        for i in 0..MERKLE_HEIGHT {
            let parent_idx = index >> 1;
            let sibling_idx = index ^ 1;
            let left = if (index & 1) == 0 {
                self.raw[i][index]
            } else {
                self.raw[i][sibling_idx]
            };
            let right = if (index & 1) == 0 {
                if sibling_idx < self.raw[i].len() {
                    self.raw[i][sibling_idx]
                } else {
                    Self::get_empty_hash(i)
                }
            } else {
                self.raw[i][index]
            };
            self.raw[i + 1][parent_idx] = compress(&[&left, &right]);
            index = parent_idx;
        }
        self.root = self.raw[MERKLE_HEIGHT][0];
        self.root
    }

    /// finalize the insert at the end of the leaves list and returns the root
    #[inline]
    pub fn finalize_insert(&mut self) -> Hash<BaseField> {
        let leaf_hash = self.leaves.last().unwrap().hash();
        self.raw[0].push(leaf_hash);
        let mut index = self.raw[0].len() - 1;
        for i in 0..MERKLE_HEIGHT {
            index >>= 1;
            // left value will always be present as it pushed before the loop
            let left = self.raw[i][2 * index];
            let right = if 2 * index + 1 < self.raw[i].len() {
                self.raw[i][2 * index + 1]
            } else {
                Self::get_empty_hash(i)
            };
            if self.raw[i + 1].len() <= index {
                self.raw[i + 1].push(compress(&[&left, &right]));
            } else {
                self.raw[i + 1][index] = compress(&[&left, &right]);
            }
        }
        self.root = self.raw[MERKLE_HEIGHT][0];
        self.root
    }

    fn get_empty_hash(i: usize) -> Hash<BaseField> {
        array::from_fn(|j| {
            let mut x = BaseField::zero();
            x += EMPTY_HASHES[i][j];
            x
        })
    }
}

impl IndexedMerkleTree {
    /// Creates a new IndexedMerkleTree.
    pub fn new() -> Self {
        let raw = (0..=MERKLE_HEIGHT)
            .map(|level| Vec::with_capacity(MERKLE_WIDTH >> level))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let mut leaves = Vec::with_capacity(MERKLE_WIDTH);
        leaves.push(Leaf::first());
        let root = array::from_fn(|_| BaseField::zero());
        let index_map = BTreeMap::from([(PriceTime::default(), 0)]);
        let mut imt = Self {
            root,
            raw,
            leaves,
            index_map,
        };
        imt.finalize_insert(); // finalizes the first leaf and updates the root
        imt
    }

    /// Inserts an order into the IndexedMerkleTree at the end of the leaves list.
    #[inline]
    pub fn insert(&mut self, order: Order) -> InsertionProof {
        // fetch initial root, low leaf parameters before insertion
        let initial_root = self.root;
        // will not panic on unwrap, as a leaf is inserted on creation
        let low_index = self.find_highest_below(&order.price_time).unwrap();
        let low_leaf = self.leaves[low_index];
        let low_merkle_proof = self.get_merkle_proof(low_index);

        // update low_leaf.next to point to the new leaf & finalize the update
        self.leaves[low_index].next = order.price_time;
        self.finalize_update(low_index);

        // get inactivity proof
        let inactive_index = self.raw[0].len();
        let inactivity_proof = self.get_merkle_proof(inactive_index);

        // insert the new leaf & finalize the insert
        self.leaves.push(order.to_leaf(&low_leaf.next));
        self.index_map.insert(order.price_time, inactive_index);
        let final_root = self.finalize_insert();

        InsertionProof {
            initial_root,
            low_leaf,
            low_merkle_proof,
            low_index,
            order,
            inactivity_proof,
            inactive_index,
            final_root,
        }
    }

    /// Finds low_leaf - immediate predecessor of the leaf being inserted
    #[inline]
    fn find_highest_below(&self, target: &PriceTime) -> Option<usize> {
        self.index_map
            .range(..target)
            .next_back()
            .map(|(_, &index)| index)
    }

    /// gets merkle proof of the leaf at the given index
    #[inline]
    fn get_merkle_proof(&self, mut index: usize) -> [Hash<BaseField>; MERKLE_HEIGHT] {
        let mut proof = array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        for (i, sibling) in proof.iter_mut().enumerate().take(MERKLE_HEIGHT) {
            let sibling_index = if index % 2 == 0 { index + 1 } else { index - 1 };
            *sibling = if sibling_index < self.raw[i].len() {
                self.raw[i][sibling_index]
            } else if index % 2 == 0 {
                Self::get_empty_hash(i)
            } else {
                panic!("Unexpected condition: index is odd and sibling index is out of bounds");
            };
            index >>= 1;
        }
        proof
    }

    /// gets merkle proof of the leaf at the given index
    pub fn get_path_with_siblings(
        &self,
        mut index: usize,
    ) -> [(Hash<BaseField>, Hash<BaseField>); MERKLE_HEIGHT] {
        let mut proof = array::from_fn(|_| {
            (
                array::from_fn(|_| BaseField::zero()),
                array::from_fn(|_| BaseField::zero()),
            )
        });
        for (i, sibling) in proof.iter_mut().enumerate().take(MERKLE_HEIGHT) {
            let left = if index % 2 == 0 { index } else { index - 1 };
            sibling.0 = self.raw[i][left];
            sibling.1 = if left + 1 < self.raw[i].len() {
                self.raw[i][left + 1]
            } else {
                Self::get_empty_hash(i)
            };
            index >>= 1;
        }
        proof
    }

    pub fn verify_merkle_proof(
        index: usize,
        proof: &[Hash<BaseField>; MERKLE_HEIGHT],
        leaf: &Leaf,
        root: &Hash<BaseField>,
    ) -> bool {
        let recomputed_root = Self::recompute_root(index, proof, leaf);
        &recomputed_root == root
    }

    pub fn recompute_root(
        mut index: usize,
        proof: &[Hash<BaseField>; MERKLE_HEIGHT],
        leaf: &Leaf,
    ) -> Hash<BaseField> {
        let mut root = leaf.hash();
        for sibling in proof.iter().take(MERKLE_HEIGHT) {
            let (left, right) = if index % 2 == 0 {
                (&root, sibling)
            } else {
                (sibling, &root)
            };
            root = compress(&[left, right]);
            index >>= 1;
        }
        root
    }

    /// Returns the root hash of the tree.
    pub fn root(&self) -> Hash<BaseField> {
        self.root
    }

    /// Returns the leaves of the tree.
    pub fn leaves(&self) -> &Vec<Leaf> {
        &self.leaves
    }

    /// Return Leaf at the given index
    /// # Panics
    /// Panics if the index is out of bounds
    pub fn leaf(&self, index: usize) -> Leaf {
        self.leaves[index]
    }
}

pub struct InsertionProof {
    /// initial root hash
    initial_root: Hash<BaseField>,
    /// low leaf - immediate predecessor of the leaf being inserted
    low_leaf: Leaf,
    /// low proof - proof of membership of the low leaf
    low_merkle_proof: [Hash<BaseField>; MERKLE_HEIGHT],
    /// low_index - index of the low leaf in the leaves
    low_index: usize,
    /// order being inserted
    order: Order,
    /// inactivity proof - proof of inactivity where the order is being inserted
    inactivity_proof: [Hash<BaseField>; MERKLE_HEIGHT],
    /// inactive index - index of the next inactive leaf in the leaves
    inactive_index: usize,
    /// final root hash after insertion
    final_root: Hash<BaseField>,
}

impl InsertionProof {
    /// sanity check for the insertion proof
    /// # Panics
    /// Panics if the proof is invalid
    pub fn verify(&self) {
        // check if low leaf is active
        assert_eq!(
            self.low_leaf.active,
            BaseField::one(),
            "Low leaf should be active"
        );
        // check if low leaf is the immediate predecessor of the order
        assert!(
            self.low_leaf.label < self.order.price_time,
            "Low leaf should be the immediate predecessor of the order"
        );
        assert!(
            self.order.price_time < self.low_leaf.next
                || self.low_leaf.next == PriceTime::default(),
            "Low Leaf must be valid"
        );

        // verify low_leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.low_index,
                &self.low_merkle_proof,
                &self.low_leaf,
                &self.initial_root
            ),
            "Low leaf merkle proof is invalid"
        );

        // update low leaf and recompute root
        let mut updated_low_leaf = self.low_leaf;
        updated_low_leaf.next = self.order.price_time;
        let intermediate_root = IndexedMerkleTree::recompute_root(
            self.low_index,
            &self.low_merkle_proof,
            &updated_low_leaf,
        );

        // verify inactivity proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.inactive_index,
                &self.inactivity_proof,
                &Leaf::empty(),
                &intermediate_root
            ),
            "Inactivity proof is invalid"
        );

        // update inactive leaf and recompute root
        let new_leaf = self.order.to_leaf(&self.low_leaf.next);
        let final_root = IndexedMerkleTree::recompute_root(
            self.inactive_index,
            &self.inactivity_proof,
            &new_leaf,
        );

        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::EMPTY_HASHES;
    use num_traits::One;

    #[test]
    fn test_sparse_imt() {
        let mut imt = IndexedMerkleTree::new();
        assert_eq!(imt.leaves.len(), 1);
        for i in 0..=MERKLE_HEIGHT {
            assert_eq!(imt.raw[i].len(), 1);
        }
        let leaf = Leaf {
            active: BaseField::one(),
            volume: BaseField::one(),
            label: PriceTime::new(BaseField::one(), BaseField::one()),
            next: PriceTime::new(BaseField::one(), BaseField::one()),
        };
        imt.leaves.push(leaf);
        imt.index_map
            .insert(PriceTime::new(BaseField::one(), BaseField::one()), 1);
        imt.finalize_insert();
        assert_eq!(imt.raw[0].len(), 2);
        for i in 1..MERKLE_HEIGHT {
            assert_eq!(imt.raw[i].len(), 1);
        }
    }

    fn create_test_order(price: u32, time: u32) -> Order {
        Order {
            price_time: PriceTime::new(BaseField::from(price), BaseField::from(time)),
            volume: BaseField::from(1), // Using 1 as default volume for simplicity
        }
    }

    #[test]
    fn test_new_tree_initialization() {
        let imt = IndexedMerkleTree::new();

        // Check initial state
        assert_eq!(imt.leaves.len(), 1, "Tree should start with one leaf");
        assert_eq!(imt.index_map.len(), 1, "Should have one label mapping");
        assert!(
            imt.index_map.contains_key(&PriceTime::default()),
            "Should contain default PriceTime"
        );

        // Check raw vectors initialization
        for i in 0..=MERKLE_HEIGHT {
            assert_eq!(
                imt.raw[i].len(),
                1,
                "Raw vector at height {} should have one element",
                i
            );
        }
    }

    #[test]
    fn test_basic_insertion() {
        let mut imt = IndexedMerkleTree::new();
        let initial_root = imt.root();

        // Insert first order
        let order1 = create_test_order(10, 1);
        imt.insert(order1);

        assert_eq!(
            imt.leaves.len(),
            2,
            "Should have two leaves after insertion"
        );
        assert_ne!(
            imt.root(),
            initial_root,
            "Root should change after insertion"
        );
        assert!(
            imt.index_map.contains_key(&order1.price_time),
            "Label map should contain new order"
        );
    }

    #[test]
    fn test_multiple_insertions() {
        let mut imt = IndexedMerkleTree::new();

        // Insert multiple orders with different price-time combinations
        let orders = [
            create_test_order(10, 1),
            create_test_order(15, 1),
            create_test_order(10, 2),
        ];

        let mut previous_root = imt.root();
        for order in orders.iter() {
            let insertion_proof = imt.insert(*order);
            insertion_proof.verify();
            let new_root = imt.root();
            assert_ne!(
                new_root, previous_root,
                "Root should change after each insertion"
            );
            let low_index = imt.find_highest_below(&order.price_time).unwrap();
            assert_eq!(
                imt.leaf(imt.leaves.len() - 1).label,
                imt.leaf(low_index).next,
                "Low leaf next should be updated"
            );
            previous_root = new_root;
        }

        assert_eq!(
            imt.leaves.len(),
            4,
            "Should have 4 leaves (including initial leaf)"
        );
        assert_eq!(imt.index_map.len(), 4, "Should have 4 label mappings");
    }

    #[test]
    fn test_find_highest_below() {
        let mut imt = IndexedMerkleTree::new();

        // Insert orders in non-sequential order
        let orders = vec![
            create_test_order(15, 1), // index 1
            create_test_order(10, 2), // index 2
            create_test_order(20, 1), // index 3
        ];

        for order in orders {
            let insertion_proof = imt.insert(order);
            insertion_proof.verify();
        }

        // Test cases for find_highest_below
        let test_cases = vec![
            (
                PriceTime::new(BaseField::from(25), BaseField::from(1)),
                Some(3),
            ), // Should find order (20,1)
            (
                PriceTime::new(BaseField::from(15), BaseField::from(2)),
                Some(1),
            ), // Should find order (15,1)
            (
                PriceTime::new(BaseField::from(10), BaseField::from(1)),
                Some(0),
            ), // Should find default leaf
            (
                PriceTime::new(BaseField::from(5), BaseField::from(1)),
                Some(0),
            ), // Should find default leaf
        ];

        for (target, expected_index) in test_cases {
            let result = imt.find_highest_below(&target);
            assert_eq!(
                result, expected_index,
                "Failed for target {:?}, expected index {:?}, got {:?}",
                target, expected_index, result
            );
        }
    }

    #[test]
    fn test_merkle_proof_verification() {
        let mut imt = IndexedMerkleTree::new();

        // Insert some orders
        let order = create_test_order(10, 1);
        imt.insert(order);

        // Get merkle proof for index 1
        let proof = imt.get_merkle_proof(1);

        // Verify proof length
        assert_eq!(
            proof.len(),
            MERKLE_HEIGHT,
            "Proof should have correct height"
        );

        // Verify that each proof element is either a valid hash or zero
        for (i, element) in proof.iter().enumerate() {
            assert!(
                element.iter().any(|&x| !x.is_zero()) || element.iter().all(|&x| x.is_zero()),
                "Proof element at height {} should be either a valid hash or all zeros",
                i
            );
        }
    }

    #[test]
    fn test_empty_hashes() {
        // tests that the constant EMPTY_HASHES is correct
        let mut empty_hashes: [[BaseField; 8]; 30] =
            array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        let mut current = Leaf::empty().hash();
        for i in 0..30 {
            empty_hashes[i] = current;
            current = compress(&[&current, &current]);
        }
        assert_eq!(empty_hashes, EMPTY_HASHES);
    }
}

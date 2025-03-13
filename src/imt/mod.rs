use crate::{
    constants::EMPTY_HASHES, executor::record::ExecutionTrace, hash::compress, types::Volume,
};
use error::IMTError;
use leaf::{Leaf, PriceTime};
use num_traits::{One, Zero};
use order::Order;
use side::{Buy, OrderSide, Sell};
use std::{array, collections::BTreeMap};
use stwo_prover::core::fields::m31::BaseField;

pub mod error;
pub mod leaf;
pub mod order;
pub mod side;

/// A Merkle proof consisting of the sibling hashes for each level from the leaf to the root.
pub type MerkleProof<F> = [Hash<F>; MERKLE_HEIGHT];
/// A Merkle path consisting of the resulting hash at each level from the leaf to the root.
pub type MerklePath<F> = [Hash<F>; MERKLE_HEIGHT + 1];
/// LeafFelts is an array of felts representing the leaf node.
pub type LeafFelts<F> = [F; N_LEAF_FELTS];
/// Hash contain 8 BaseField elements.
pub type Hash<F> = [F; 8];
pub const MERKLE_HEIGHT: usize = 20;
pub const MERKLE_WIDTH: usize = 1 << MERKLE_HEIGHT; // number of leaves at the bottom of the tree
pub const N_LEAF_FELTS: usize = 41; // number of felts in a leaf
pub const N_U64_FELTS: usize = 8; // number of felts in a u64
pub const N_ORDER_FELTS: usize = 3 * N_U64_FELTS; // order contains Price(8Felts), Volume(8Felts), Time(8Felts)

/// A structure representing an Indexed Merkle Tree for order books.
///
/// An Indexed Merkle Tree is a variant of the Merkle Tree data structure
/// that includes metadata along with other parts of Node Leaf to ensure
/// efficient non-membership proofs.
///
/// This implementation supports two types of order trees:
/// - `BuyIMT`: Orders are arranged with higher prices having priority (descending price order)
/// - `SellIMT`: Orders are arranged with lower prices having priority (ascending price order)
///
/// The PriceTime ordering is critical for maintaining correct market matching behavior:
/// - In BuyIMT, higher price offers have precedence (if prices are equal, earlier time wins)
/// - In SellIMT, lower price offers have precedence (if prices are equal, earlier time wins)
///
/// # Examples
///
/// ```
/// // Example usage of IndexedMerkleTree
/// // let buy_tree = BuyIMT::new();  // Higher prices have priority
/// // let sell_tree = SellIMT::new(); // Lower prices have priority
/// // let order = Order::new(1, 10, 1); // volume, price, time
/// // let insertion_proof = tree.insert(order);
/// // insertion_proof.verify();
/// //
/// ```
/// # References
///
/// - [Section3, Transparency Dictionaries with Succinct Proofs of Correct Operation](https://eprint.iacr.org/2021/1263.pdf)
pub struct IndexedMerkleTree<'a, S> {
    /// The root hash of the tree.
    root: Hash<BaseField>,
    /// raw data
    /// raw[0] is the leaf hashes, raw[1] is the first level of the tree, etc.
    raw: Box<[Vec<Hash<BaseField>>]>,
    /// leaves of the tree containing orders and metadata
    leaves: Vec<Leaf<BaseField, S>>,
    /// label to indices for quick lookups
    index_map: BTreeMap<PriceTime<BaseField, S>, usize>,
    /// trace records the operations on the tree
    trace: &'a mut ExecutionTrace<BaseField>,
}

pub type SellIMT<'a> = IndexedMerkleTree<'a, Sell>;
pub type BuyIMT<'a> = IndexedMerkleTree<'a, Buy>;

impl<S: OrderSide> IndexedMerkleTree<'_, S> {
    /// finalize the update at given index and returns the computed hash at each level
    #[inline]
    pub fn finalize_update(&mut self, mut index: usize) -> MerklePath<BaseField> {
        let mut path = array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        let leaf_hash = self.leaves[index].hash();
        self.raw[0][index] = leaf_hash;
        path[0] = leaf_hash;
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
            self.trace.add_merkle_hash_event(left, right);
            let hash = compress(&[&left, &right]);
            self.raw[i + 1][parent_idx] = hash;
            path[i + 1] = hash;
            index = parent_idx;
        }
        self.root = self.raw[MERKLE_HEIGHT][0];
        path
    }

    /// finalize the insert at the end of the leaves list and returns the root
    #[inline]
    pub fn finalize_insert(&mut self, record_trace: bool) -> MerklePath<BaseField> {
        // will not panic on unwrap, as a leaf is inserted on creation
        let leaf_hash = self.leaves.last().unwrap().hash();
        let mut path = array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        self.raw[0].push(leaf_hash);
        path[0] = leaf_hash;
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
            if record_trace {
                self.trace.add_merkle_hash_event(left, right);
            }
            if self.raw[i + 1].len() <= index {
                let hash = compress(&[&left, &right]);
                self.raw[i + 1].push(hash);
                path[i + 1] = hash;
            } else {
                let hash = compress(&[&left, &right]);
                self.raw[i + 1][index] = hash;
                path[i + 1] = hash;
            }
        }
        self.root = self.raw[MERKLE_HEIGHT][0];
        path
    }

    /// Returns the hash of the node at the given level if the subtree contains only empty nodes.
    fn get_empty_hash(i: usize) -> Hash<BaseField> {
        array::from_fn(|j| {
            let mut x = BaseField::zero();
            x += EMPTY_HASHES[i][j];
            x
        })
    }
}

impl<'a, S: OrderSide> IndexedMerkleTree<'a, S> {
    /// Creates a new IndexedMerkleTree.
    pub fn new(trace: &'a mut ExecutionTrace<BaseField>) -> Self {
        let raw = (0..=MERKLE_HEIGHT)
            .map(|level| Vec::with_capacity(MERKLE_WIDTH >> level))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let mut leaves = Vec::with_capacity(MERKLE_WIDTH);
        leaves.push(Leaf::first());
        let root = array::from_fn(|_| BaseField::zero());
        let index_map = BTreeMap::from([(PriceTime::first(), 0)]);
        let mut imt = Self {
            root,
            raw,
            leaves,
            index_map,
            trace,
        };
        imt.finalize_insert(false); // finalizes the first leaf and updates the root
        imt
    }

    /// Inserts an order into the IndexedMerkleTree at the end of the leaves list.
    #[inline]
    pub fn insert(&mut self, order: Order<BaseField, S>) -> Result<InsertionProof<S>, IMTError> {
        // fetch initial root, low leaf parameters before insertion
        let initial_root = self.root;
        // will not panic on unwrap, as a leaf is inserted on creation
        let low_index = self.find_low(&order.price_time)?;
        let low_leaf = self.leaves[low_index];
        self.trace.add_leaf_hash_event(&low_leaf.to_felts());
        let (low_merkle_proof, low_merkle_path) = self.get_merkle_proof(low_index);

        // update low_leaf.next to point to the new leaf & finalize the update
        self.leaves[low_index].next = order.price_time;
        self.trace
            .add_leaf_hash_event(&self.leaves[low_index].to_felts());
        let low_merkle_updated_path = self.finalize_update(low_index);

        // get inactivity proof
        let inactive_index = self.raw[0].len();
        self.trace.add_leaf_hash_event(&low_leaf.to_felts());
        let (inactive_proof, inactive_path) = self.get_merkle_proof(inactive_index);

        // insert the new leaf & finalize the insert
        self.leaves.push(order.to_leaf(&low_leaf.next));
        self.trace
            .add_leaf_hash_event(&self.leaves[inactive_index].to_felts());
        self.index_map.insert(order.price_time, inactive_index);

        let inactive_updated_path = self.finalize_insert(true);
        Ok(InsertionProof {
            initial_root,
            low_leaf,
            low_merkle_proof,
            low_merkle_path,
            low_merkle_updated_path,
            low_index,
            order,
            inactive_proof,
            inactive_path,
            inactive_updated_path,
            inactive_index,
            final_root: inactive_updated_path[MERKLE_HEIGHT],
        })
    }

    /// Updates an order into the IndexedMerkleTree at the end of the leaves list.
    #[inline]
    pub fn update(
        &mut self,
        price_time: PriceTime<BaseField, S>,
        volume: Volume<BaseField>,
    ) -> Result<UpdateProof<BaseField, S>, IMTError> {
        if price_time == PriceTime::default() {
            return Err(IMTError::CannotUpdateFirstLeaf);
        }
        // fetch initial root, leaf parameters before update
        let initial_root = self.root;
        // will not panic on unwrap, as a leaf is inserted on creation
        let index = self.find(&price_time)?;
        let leaf = self.leaves[index];
        let (merkle_proof, merkle_path) = self.get_merkle_proof(index);

        // update volume to the new volume & finalize the update
        self.leaves[index].volume = volume;
        let merkle_updated_path = self.finalize_update(index);

        Ok(UpdateProof {
            initial_root,
            leaf,
            merkle_proof,
            merkle_path,
            merkle_updated_path,
            index,
            volume,
            final_root: merkle_updated_path[MERKLE_HEIGHT],
        })
    }

    /// Cancel an order into the IndexedMerkleTree at the end of the leaves list.
    #[inline]
    pub fn cancel_at_index(&mut self, index: usize) -> Result<CancellationProof<S>, IMTError> {
        if index == 0 {
            return Err(IMTError::CannotCancelFirstLeaf);
        }
        // fetch initial root, low leaf parameters before insertion
        let initial_root = self.root;
        let cancel_leaf = self.leaves[index];
        let low_index = self.find_low(&cancel_leaf.label)?;
        let low_leaf = self.leaves[low_index];
        let (low_merkle_proof, low_merkle_path) = self.get_merkle_proof(low_index);
        // update low_leaf.next to point to the new leaf & finalize the update
        self.leaves[low_index].next = cancel_leaf.next;
        let low_merkle_updated_path = self.finalize_update(low_index);
        // get cancel leaf proof.
        let (cancel_proof, cancel_path) = self.get_merkle_proof(index);
        // update cancel leaf to inactive & finalize the update
        self.leaves[index].active = BaseField::zero();
        let cancel_updated_path = self.finalize_update(index);
        // remove from index map
        self.index_map.remove(&cancel_leaf.label);
        Ok(CancellationProof {
            initial_root,
            low_leaf,
            low_merkle_proof,
            low_merkle_path,
            low_merkle_updated_path,
            low_index,
            cancel_leaf,
            cancel_leaf_proof: cancel_proof,
            cancel_leaf_path: cancel_path,
            cancel_leaf_updated_path: cancel_updated_path,
            cancel_leaf_index: index,
            final_root: cancel_updated_path[MERKLE_HEIGHT],
        })
    }

    /// Matches an order of highest priority.
    #[inline]
    pub fn match_order(&mut self) -> Result<MatchProof<S>, IMTError> {
        // fetch initial root, low leaf parameters before insertion
        let initial_root = self.root;
        let index = self.find(&self.leaves[0].next)?;
        let match_leaf = self.leaves[index];
        let (low_merkle_proof, low_merkle_path) = self.get_merkle_proof(0);
        // update low_leaf.next to point to the new leaf & finalize the update
        self.leaves[0].next = match_leaf.next;
        let low_merkle_updated_path = self.finalize_update(0);
        // get match leaf proof.
        let (match_proof, match_path) = self.get_merkle_proof(index);
        // update cancel leaf to inactive & finalize the update
        self.leaves[index].active = BaseField::zero();
        let match_updated_path = self.finalize_update(index);
        // remove from index map
        self.index_map.remove(&match_leaf.label);
        Ok(MatchProof {
            initial_root,
            low_merkle_proof,
            low_merkle_path,
            low_merkle_updated_path,
            match_leaf,
            match_leaf_proof: match_proof,
            match_leaf_path: match_path,
            match_leaf_updated_path: match_updated_path,
            match_leaf_index: index,
            final_root: match_updated_path[MERKLE_HEIGHT],
        })
    }

    /// Partial Matches an order of highest priority.
    #[inline]
    pub fn match_partially(&mut self, volume: u64) -> Result<PartialMatchProof<S>, IMTError> {
        // fetch initial root, low leaf parameters before insertion
        let filled_volume = Volume::from_u64(volume);
        let initial_root = self.root;
        let index = self.find(&self.leaves[0].next)?;
        let p_match_leaf = self.leaves[index];
        let (low_merkle_proof, low_merkle_path) = self.get_merkle_proof(0);
        // get match leaf proof.
        let (p_match_proof, p_match_path) = self.get_merkle_proof(index);
        // check if the leaf has enough volume to fill
        if p_match_leaf.volume < filled_volume {
            return Err(IMTError::InsufficientVolumeToFill(
                volume,
                p_match_leaf.volume.to_u64(),
            ));
        }
        // update volume to the new volume & finalize the update
        let remaining_volume = p_match_leaf.volume - filled_volume;
        self.leaves[index].volume = remaining_volume;
        let match_updated_path = self.finalize_update(index);
        Ok(PartialMatchProof {
            initial_root,
            low_merkle_proof,
            low_merkle_path,
            p_match_leaf,
            p_match_leaf_proof: p_match_proof,
            p_match_leaf_path: p_match_path,
            p_match_leaf_updated_path: match_updated_path,
            p_match_leaf_index: index,
            final_root: match_updated_path[MERKLE_HEIGHT],
            remaining_volume,
            filled_volume,
        })
    }

    /// Finds low_leaf - immediate predecessor of the leaf being inserted
    #[inline]
    fn find_low(&self, target: &PriceTime<BaseField, S>) -> Result<usize, IMTError> {
        self.index_map
            .range(..target)
            .next_back()
            .map(|(_, &index)| index)
            .ok_or(IMTError::LowLeafNotFound)
    }

    /// Finds the index of the leaf in the tree which has the given Price, Time.
    #[inline]
    fn find(&self, key: &PriceTime<BaseField, S>) -> Result<usize, IMTError> {
        self.index_map
            .get(key)
            .copied()
            .ok_or(IMTError::LeafNotFound)
    }

    /// gets merkle proof of the leaf at the given index
    #[inline]
    fn get_merkle_proof(
        &mut self,
        mut index: usize,
    ) -> (MerkleProof<BaseField>, MerklePath<BaseField>) {
        let mut proof = array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        let mut path = array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        path[0] = if index >= self.raw[0].len() {
            Self::get_empty_hash(0)
        } else {
            self.raw[0][index]
        };
        for (i, sibling) in proof.iter_mut().enumerate().take(MERKLE_HEIGHT) {
            let sibling_index = if index % 2 == 0 { index + 1 } else { index - 1 };
            *sibling = if sibling_index < self.raw[i].len() {
                self.raw[i][sibling_index]
            } else if index % 2 == 0 {
                Self::get_empty_hash(i)
            } else {
                panic!("Unexpected condition: index is odd and sibling index is out of bounds");
            };
            if index % 2 == 0 {
                self.trace.add_merkle_hash_event(path[i], *sibling);
            } else {
                self.trace.add_merkle_hash_event(*sibling, path[i]);
            }
            index >>= 1;
            path[i + 1] = *self.raw[i + 1]
                .get(index)
                .unwrap_or(&Self::get_empty_hash(i + 1));
        }
        (proof, path)
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
        proof: &MerkleProof<BaseField>,
        path: &MerklePath<BaseField>,
        leaf: &Leaf<BaseField, S>,
        root: &Hash<BaseField>,
    ) -> bool {
        let recomputed_root = Self::recompute_root(index, proof, path, leaf);
        &recomputed_root == root
    }

    pub fn recompute_root(
        mut index: usize,
        proof: &MerkleProof<BaseField>,
        path: &MerklePath<BaseField>,
        leaf: &Leaf<BaseField, S>,
    ) -> Hash<BaseField> {
        let mut root = leaf.hash();
        assert_eq!(path[0], root, "Path 0 should be the leaf hash");
        for (sibling, hash) in proof.iter().zip(path.iter().skip(1)) {
            let (left, right) = if index % 2 == 0 {
                (&root, sibling)
            } else {
                (sibling, &root)
            };
            root = compress(&[left, right]);
            assert_eq!(root, *hash, "Parent hash should match the path hash");
            index >>= 1;
        }
        root
    }

    /// Returns the root hash of the tree.
    pub fn root(&self) -> Hash<BaseField> {
        self.root
    }

    /// Returns the leaves of the tree.
    pub fn leaves(&self) -> &Vec<Leaf<BaseField, S>> {
        &self.leaves
    }

    /// Return Leaf<BaseField> at the given index
    /// # Panics
    /// Panics if the index is out of bounds
    pub fn leaf(&self, index: usize) -> Leaf<BaseField, S> {
        self.leaves[index]
    }
}

pub struct InsertionProof<S> {
    /// initial root hash
    initial_root: Hash<BaseField>,
    /// low leaf - immediate predecessor of the leaf being inserted
    low_leaf: Leaf<BaseField, S>,
    /// low proof - proof of membership of the low leaf
    low_merkle_proof: MerkleProof<BaseField>,
    /// low merkle path containing the resulting hash at each level of the tree
    low_merkle_path: MerklePath<BaseField>,
    /// low merkle update path is the resulting hash at each level of the tree
    /// after updating the low leaf
    low_merkle_updated_path: MerklePath<BaseField>,
    /// low_index - index of the low leaf in the leaves
    low_index: usize,
    /// order being inserted
    order: Order<BaseField, S>,
    /// inactivity proof - proof of inactivity where the order is being inserted
    inactive_proof: MerkleProof<BaseField>,
    /// inactivity path is the resulting hash at each level of the tree
    inactive_path: MerklePath<BaseField>,
    /// inactivity update compute is the resulting hash at each level of the tree
    /// after updating the inactive leaf
    inactive_updated_path: MerklePath<BaseField>,
    /// inactive index - index of the next inactive leaf in the leaves
    inactive_index: usize,
    /// final root hash after insertion
    final_root: Hash<BaseField>,
}

impl<S: OrderSide> InsertionProof<S> {
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
            "Low Leaf<BaseField> must be valid"
        );

        // verify low_leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.low_index,
                &self.low_merkle_proof,
                &self.low_merkle_path,
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
            &self.low_merkle_updated_path,
            &updated_low_leaf,
        );

        let empty_leaf: Leaf<BaseField, S> = Leaf::empty();

        // verify inactivity proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.inactive_index,
                &self.inactive_proof,
                &self.inactive_path,
                &empty_leaf,
                &intermediate_root
            ),
            "Inactivity proof is invalid"
        );

        // update inactive leaf and recompute root
        let new_leaf = self.order.to_leaf(&self.low_leaf.next);
        let final_root = IndexedMerkleTree::recompute_root(
            self.inactive_index,
            &self.inactive_proof,
            &self.inactive_updated_path,
            &new_leaf,
        );

        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

pub struct UpdateProof<F, S> {
    /// initial root hash
    initial_root: Hash<F>,
    /// low leaf - immediate predecessor of the leaf being inserted
    leaf: Leaf<F, S>,
    /// low proof - proof of membership of the low leaf
    merkle_proof: [Hash<F>; MERKLE_HEIGHT],
    /// low merkle path containing the resulting hash at each level of the tree
    merkle_path: [Hash<F>; MERKLE_HEIGHT + 1],
    /// new volume
    volume: Volume<F>,
    /// low merkle update path is the resulting hash at each level of the tree
    /// after updating the low leaf
    merkle_updated_path: [Hash<F>; MERKLE_HEIGHT + 1],
    /// low_index - index of the low leaf in the leaves
    index: usize,
    /// final root hash after insertion
    final_root: Hash<F>,
}

impl<S: OrderSide> UpdateProof<BaseField, S> {
    /// sanity check for the update proof
    /// # Panics
    /// Panics if the proof is invalid
    pub fn verify(&self) {
        // check if leaf is active
        assert_eq!(
            self.leaf.active,
            BaseField::one(),
            "Low leaf should be active"
        );

        // verify leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.index,
                &self.merkle_proof,
                &self.merkle_path,
                &self.leaf,
                &self.initial_root
            ),
            "Low leaf merkle proof is invalid"
        );

        // update low leaf and recompute root
        let mut updated_low_leaf = self.leaf;
        updated_low_leaf.volume = self.volume;
        let final_root = IndexedMerkleTree::recompute_root(
            self.index,
            &self.merkle_proof,
            &self.merkle_updated_path,
            &updated_low_leaf,
        );

        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

pub struct CancellationProof<S> {
    /// initial root hash
    pub initial_root: Hash<BaseField>,
    /// low leaf - immediate predecessor of the leaf being cancelled
    pub low_leaf: Leaf<BaseField, S>,
    /// low proof - proof of membership of the low leaf
    pub low_merkle_proof: MerkleProof<BaseField>,
    /// low merkle path containing the resulting hash at each level of the tree
    pub low_merkle_path: MerklePath<BaseField>,
    /// low merkle update path is the resulting hash at each level of the tree
    /// after updating the low leaf
    pub low_merkle_updated_path: MerklePath<BaseField>,
    /// low_index - index of the low leaf in the leaves
    pub low_index: usize,
    /// leaf containing order tjat is being cancelled
    pub cancel_leaf: Leaf<BaseField, S>,
    /// inactivity proof - proof of inactivity where the order is being inserted
    pub cancel_leaf_proof: MerkleProof<BaseField>,
    /// inactivity path is the resulting hash at each level of the tree
    pub cancel_leaf_path: MerklePath<BaseField>,
    /// inactivity update compute is the resulting hash at each level of the tree
    /// after updating the inactive leaf
    pub cancel_leaf_updated_path: MerklePath<BaseField>,
    /// inactive index - index of the next inactive leaf in the leaves
    pub cancel_leaf_index: usize,
    /// final root hash after insertion
    pub final_root: Hash<BaseField>,
}
impl<S: OrderSide> CancellationProof<S> {
    /// sanity check for the cancellation proof
    /// # Panics
    /// Panics if the proof is invalid
    pub fn verify(&self) {
        // check if low leaf is active
        assert_eq!(
            self.low_leaf.active,
            BaseField::one(),
            "Low leaf should be active"
        );
        // verify low_leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.low_index,
                &self.low_merkle_proof,
                &self.low_merkle_path,
                &self.low_leaf,
                &self.initial_root
            ),
            "Low leaf merkle proof is invalid"
        );
        // update low leaf and recompute root
        let mut updated_low_leaf = self.low_leaf;
        updated_low_leaf.next = self.cancel_leaf.next;
        let intermediate_root = IndexedMerkleTree::recompute_root(
            self.low_index,
            &self.low_merkle_proof,
            &self.low_merkle_updated_path,
            &updated_low_leaf,
        );
        // verify inactivity proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.cancel_leaf_index,
                &self.cancel_leaf_proof,
                &self.cancel_leaf_path,
                &self.cancel_leaf,
                &intermediate_root
            ),
            "Inactivity proof is invalid"
        );
        // update inactive leaf and recompute root
        let mut new_leaf = self.cancel_leaf;
        new_leaf.active = BaseField::zero();
        let final_root = IndexedMerkleTree::recompute_root(
            self.cancel_leaf_index,
            &self.cancel_leaf_proof,
            &self.cancel_leaf_updated_path,
            &new_leaf,
        );
        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

pub struct MatchProof<S> {
    /// initial root hash
    pub initial_root: Hash<BaseField>,
    /// low leaf indicated the first leaf in the order tree.
    /// low proof - proof of membership of the low leaf
    pub low_merkle_proof: MerkleProof<BaseField>,
    /// low merkle path containing the resulting hash at each level of the tree
    pub low_merkle_path: MerklePath<BaseField>,
    /// low merkle update path is the resulting hash at each level of the tree
    /// after updating the low leaf
    pub low_merkle_updated_path: MerklePath<BaseField>,
    /// leaf containing order tjat is being cancelled
    pub match_leaf: Leaf<BaseField, S>,
    /// inactivity proof - proof of inactivity where the order is being inserted
    pub match_leaf_proof: MerkleProof<BaseField>,
    /// inactivity path is the resulting hash at each level of the tree
    pub match_leaf_path: MerklePath<BaseField>,
    /// inactivity update compute is the resulting hash at each level of the tree
    /// after updating the inactive leaf
    pub match_leaf_updated_path: MerklePath<BaseField>,
    /// inactive index - index of the next inactive leaf in the leaves
    pub match_leaf_index: usize,
    /// final root hash after insertion
    pub final_root: Hash<BaseField>,
}
impl<S: OrderSide> MatchProof<S> {
    /// sanity check for the cancellation proof
    /// # Panics
    /// Panics if the proof is invalid
    pub fn verify(&self) {
        let mut low: Leaf<BaseField, S> = Leaf::first();
        low.next = self.match_leaf.label;
        // verify low_leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                0,
                &self.low_merkle_proof,
                &self.low_merkle_path,
                &low,
                &self.initial_root
            ),
            "Low leaf merkle proof is invalid"
        );
        // update low leaf and recompute root
        low.next = self.match_leaf.next;
        let intermediate_root = IndexedMerkleTree::recompute_root(
            0,
            &self.low_merkle_proof,
            &self.low_merkle_updated_path,
            &low,
        );
        // verify matched leaf's proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.match_leaf_index,
                &self.match_leaf_proof,
                &self.match_leaf_path,
                &self.match_leaf,
                &intermediate_root
            ),
            "Inactivity proof is invalid"
        );
        // update inactive leaf and recompute root
        let mut new_leaf = self.match_leaf;
        new_leaf.active = BaseField::zero();
        let final_root = IndexedMerkleTree::recompute_root(
            self.match_leaf_index,
            &self.match_leaf_proof,
            &self.match_leaf_updated_path,
            &new_leaf,
        );
        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

pub struct PartialMatchProof<S> {
    /// initial root hash
    pub initial_root: Hash<BaseField>,
    /// low leaf indicated the first leaf in the order tree.
    /// low proof - proof of membership of the low leaf
    pub low_merkle_proof: MerkleProof<BaseField>,
    /// low merkle path containing the resulting hash at each level of the tree
    pub low_merkle_path: MerklePath<BaseField>,
    /// leaf containing order that is being matches
    pub p_match_leaf: Leaf<BaseField, S>,
    /// proof of leaf where the patial matches order is present
    pub p_match_leaf_proof: MerkleProof<BaseField>,
    /// inactivity path is the resulting hash at each level of the tree
    pub p_match_leaf_path: MerklePath<BaseField>,
    /// inactivity update compute is the resulting hash at each level of the tree
    /// after updating the inactive leaf
    pub p_match_leaf_updated_path: MerklePath<BaseField>,
    /// inactive index - index of the next inactive leaf in the leaves
    pub p_match_leaf_index: usize,
    /// volume that has been filled
    pub filled_volume: Volume<BaseField>,
    /// remaining volume
    pub remaining_volume: Volume<BaseField>,
    /// final root hash after insertion
    pub final_root: Hash<BaseField>,
}
impl<S: OrderSide> PartialMatchProof<S> {
    /// sanity check for the cancellation proof
    /// # Panics
    /// Panics if the proof is invalid
    pub fn verify(&self) {
        let mut low: Leaf<BaseField, S> = Leaf::first();
        low.next = self.p_match_leaf.label;
        // verify low_leafs merkle proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                0,
                &self.low_merkle_proof,
                &self.low_merkle_path,
                &low,
                &self.initial_root
            ),
            "Low leaf merkle proof is invalid"
        );
        // verify matched leaf's proof
        assert!(
            IndexedMerkleTree::verify_merkle_proof(
                self.p_match_leaf_index,
                &self.p_match_leaf_proof,
                &self.p_match_leaf_path,
                &self.p_match_leaf,
                &self.initial_root
            ),
            "Inactivity proof is invalid"
        );
        // update inactive leaf and recompute root
        let mut new_leaf = self.p_match_leaf;
        new_leaf.volume = self.remaining_volume;
        assert_eq!(
            self.filled_volume + self.remaining_volume,
            self.p_match_leaf.volume
        );
        let final_root = IndexedMerkleTree::recompute_root(
            self.p_match_leaf_index,
            &self.p_match_leaf_proof,
            &self.p_match_leaf_updated_path,
            &new_leaf,
        );
        // check if final root is correct
        assert_eq!(final_root, self.final_root, "Final root hash is incorrect");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{constants::EMPTY_HASHES, types::Volume};
    use leaf::SellLeaf;
    use num_traits::One;

    #[test]
    fn test_sparse_imt() {
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);
        assert_eq!(imt.leaves.len(), 1);
        for i in 0..=MERKLE_HEIGHT {
            assert_eq!(imt.raw[i].len(), 1);
        }
        let leaf = Leaf {
            active: BaseField::one(),
            volume: Volume::from_u64(1),
            label: PriceTime::new(1, 1),
            next: PriceTime::new(1, 1),
        };
        imt.leaves.push(leaf);
        imt.index_map.insert(PriceTime::new(1, 1), 1);
        imt.finalize_insert(true);
        assert_eq!(imt.raw[0].len(), 2);
        for i in 1..MERKLE_HEIGHT {
            assert_eq!(imt.raw[i].len(), 1);
        }
    }

    #[test]
    fn test_new_tree_initialization() {
        let mut trace = ExecutionTrace::new();
        let imt = SellIMT::new(&mut trace);

        // Check initial state
        assert_eq!(imt.leaves.len(), 1, "Tree should start with one leaf");
        assert_eq!(imt.index_map.len(), 1, "Should have one label mapping");
        assert!(
            imt.index_map.contains_key(&PriceTime::default()),
            "Should contain default PriceTime<BaseField>"
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
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);
        let initial_root = imt.root();

        // Insert first order
        let order1 = Order::new(1, 10, 1);
        imt.insert(order1).unwrap();

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

        // number of hashes in one insertion must be 4*MERKLE_HEIGHT + 4
        assert_eq!(
            trace.poseidon_operations.len(),
            4 * MERKLE_HEIGHT + 4,
            "Number of hashes in one insertion must be 4*MERKLE_HEIGHT + 4"
        );
    }

    #[test]
    fn test_multiple_insertions() {
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);

        // Insert multiple orders with different price-time combinations
        let orders = [
            Order::new(1, 10, 1),
            Order::new(1, 15, 1),
            Order::new(1, 10, 2),
        ];

        let mut previous_root = imt.root();
        for order in orders.iter() {
            let insertion_proof = imt.insert(*order).expect("Insertion should succeed");
            insertion_proof.verify();
            let new_root = imt.root();
            assert_ne!(
                new_root, previous_root,
                "Root should change after each insertion"
            );
            let low_index = imt.find_low(&order.price_time).unwrap();
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
    fn test_find_low() {
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);

        // Insert orders in non-sequential order
        let orders = vec![
            Order::new(1, 15, 1), // index 1
            Order::new(1, 10, 2), // index 2
            Order::new(1, 20, 1), // index 3
        ];

        for order in orders {
            let insertion_proof = imt.insert(order).expect("Insertion should succeed");
            insertion_proof.verify();
        }

        // Test cases for find_low
        let test_cases = vec![
            (PriceTime::new(25, 1), 3), // Should find order (20,1)
            (PriceTime::new(15, 2), 1), // Should find order (15,1)
            (PriceTime::new(10, 1), 0), // Should find default leaf
            (PriceTime::new(5, 1), 0),  // Should find default leaf
        ];

        for (target, expected_index) in test_cases {
            let result = imt.find_low(&target).unwrap();
            assert_eq!(
                result, expected_index,
                "Failed for target {:?}, expected index {:?}, got {:?}",
                target, expected_index, result
            );
        }
    }

    #[test]
    fn test_merkle_proof_verification() {
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);

        // Insert some orders
        let order = Order::new(1, 10, 1);
        imt.insert(order).unwrap();

        // Get merkle proof for index 1
        let (proof, _) = imt.get_merkle_proof(1);

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
    fn test_update_volume() {
        let mut trace = ExecutionTrace::new();
        let mut imt = SellIMT::new(&mut trace);

        // Insert some orders
        let order1 = Order::new(1, 10, 1);
        let order2 = Order::new(1, 15, 1);
        let order3 = Order::new(1, 10, 2);
        imt.insert(order1).unwrap();
        imt.insert(order2).unwrap();
        imt.insert(order3).unwrap();

        // Update the volume of the first order
        let new_volume = Volume::from_u64(2);
        let update_proof = imt
            .update(order1.price_time, new_volume)
            .expect("Update should succeed");
        update_proof.verify();

        // Check that the volume of the first order has been updated
        let updated_leaf = imt.leaf(1);
        assert_eq!(updated_leaf.volume, new_volume, "Volume should be updated");
    }

    #[test]
    fn test_empty_hashes() {
        // tests that the constant EMPTY_HASHES is correct
        let mut empty_hashes: [[BaseField; 8]; 30] =
            array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        let mut current = SellLeaf::empty().hash();
        for i in 0..30 {
            empty_hashes[i] = current;
            current = compress(&[&current, &current]);
        }
        assert_eq!(empty_hashes, EMPTY_HASHES);
    }

    #[test]
    fn test_buy_imt_initialization() {
        let mut trace = ExecutionTrace::new();
        let imt = BuyIMT::new(&mut trace);

        // Check initial state
        assert_eq!(imt.leaves.len(), 1, "Tree should start with one leaf");
        assert_eq!(imt.index_map.len(), 1, "Should have one label mapping");
        assert!(
            imt.index_map.contains_key(&PriceTime::first()),
            "Should contain first PriceTime<BaseField>"
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
    fn test_buy_imt_basic_insertion() {
        let mut trace = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut trace);
        let initial_root = imt.root();

        // Insert first order
        let order1 = Order::new(1, 10, 1);
        println!("{:?}", imt.leaves);
        imt.insert(order1).unwrap();

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
    fn test_buy_imt_multiple_insertions() {
        let mut trace = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut trace);

        // Insert multiple orders with different price-time combinations
        let orders = [
            Order::new(1, 10, 1),
            Order::new(1, 15, 1),
            Order::new(1, 10, 2),
        ];

        let mut previous_root = imt.root();
        for order in orders.iter() {
            let insertion_proof = imt.insert(*order).expect("Insertion should succeed");
            insertion_proof.verify();
            let new_root = imt.root();
            assert_ne!(
                new_root, previous_root,
                "Root should change after each insertion"
            );
            let low_index = imt.find_low(&order.price_time).unwrap();
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
    fn test_buy_imt_find_low() {
        let mut trace = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut trace);

        // Insert orders in non-sequential order
        let orders = vec![
            Order::new(1, 15, 1), // index 1
            Order::new(1, 10, 2), // index 2
            Order::new(1, 20, 1), // index 3
        ];

        for order in orders {
            let insertion_proof = imt.insert(order).expect("Insertion should succeed");
            insertion_proof.verify();
        }

        // Test cases for find_low
        let test_cases = vec![
            (PriceTime::new(25, 1), 0), // Should find order MAX
            (PriceTime::new(15, 2), 1), // Should find order (15,1)
            (PriceTime::new(10, 1), 1), // Should find default leaf
            (PriceTime::new(5, 1), 2),  // Should find default leaf
            (PriceTime::new(18, 1), 3), // should find order (15,1)
        ];

        for (target, expected_index) in test_cases {
            let result = imt.find_low(&target).unwrap();
            assert_eq!(
                result, expected_index,
                "Failed for target {:?}, expected index {:?}, got {:?}",
                target, expected_index, result
            );
        }
    }

    #[test]
    fn test_buy_imt_merkle_proof_verification() {
        let mut trace = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut trace);

        // Insert some orders
        let order = Order::new(1, 10, 1);
        imt.insert(order).unwrap();

        // Get merkle proof for index 1
        let (proof, _) = imt.get_merkle_proof(1);

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
    fn test_buy_imt_update_volume() {
        let mut trace = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut trace);

        // Insert some orders
        let order1 = Order::new(1, 10, 1);
        let order2 = Order::new(1, 15, 1);
        let order3 = Order::new(1, 10, 2);
        imt.insert(order1).unwrap();
        imt.insert(order2).unwrap();
        imt.insert(order3).unwrap();

        // Update the volume of the first order
        let new_volume = Volume::from_u64(2);
        let update_proof = imt
            .update(order1.price_time, new_volume)
            .expect("Update should succeed");
        update_proof.verify();

        // Check that the volume of the first order has been updated
        let updated_leaf = imt.leaf(1);
        assert_eq!(updated_leaf.volume, new_volume, "Volume should be updated");
    }

    #[test]
    fn test_buy_imt_empty_hashes() {
        // tests that the constant EMPTY_HASHES is correct
        let mut empty_hashes: [[BaseField; 8]; 30] =
            array::from_fn(|_| array::from_fn(|_| BaseField::zero()));
        let mut current = SellLeaf::empty().hash();
        for i in 0..30 {
            empty_hashes[i] = current;
            current = compress(&[&current, &current]);
        }
        assert_eq!(empty_hashes, EMPTY_HASHES);
    }
}

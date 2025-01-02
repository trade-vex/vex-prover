use std::array;

use crate::{hash::hash_leaf, imt::Hash};
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::BaseField;

#[derive(Default, Clone, Copy)]
pub struct Leaf {
    /// Determines if the leaf is active
    /// active leaf indicate whether the node contains an order eligible to be executed
    pub active: BaseField,
    /// Unfilled Volume
    pub volume: BaseField,
    /// label determines the ordering in the IMT: Price Time Priority
    pub label: PriceTime,
    /// next refers to the next leaf in the order book
    pub next: PriceTime,
}

impl Leaf {
    /// Return The first leaf of the IMT
    pub fn first() -> Self {
        Self {
            active: BaseField::one(),
            volume: BaseField::zero(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }

    /// Return inactive empty leaf
    pub fn empty() -> Self {
        Self {
            active: BaseField::zero(),
            volume: BaseField::zero(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }

    /// return true if the leaf is empty
    pub fn is_empty(&self) -> bool {
        self.active.is_zero() && self.volume.is_zero() && self.label.is_zero()
    }

    /// construct felts from leaf
    pub fn to_felts(&self) -> [BaseField; 6] {
        let mut felts = array::from_fn(|_| BaseField::zero());
        felts[0] = self.active;
        felts[1] = self.volume;
        [felts[2], felts[3]] = self.label.to_felts();
        [felts[4], felts[5]] = self.next.to_felts();
        felts
    }

    /// construct leaf from felts
    pub fn from_felts(felts: [BaseField; 6]) -> Self {
        Self {
            active: felts[0],
            volume: felts[1],
            label: PriceTime::from_felts([felts[2], felts[3]]),
            next: PriceTime::from_felts([felts[4], felts[5]]),
        }
    }

    /// poseidon hash of the leaf
    pub fn hash(&self) -> Hash<BaseField> {
        let felts = self.to_felts();
        let mut input_state = array::from_fn(|_| BaseField::zero());
        input_state[..6].clone_from_slice(&felts[..6]);
        hash_leaf(input_state)
    }
}

use std::cmp::Ordering;

// Holds a price and a time, used as a key in the BTreeMap
#[derive(Debug, Eq, Clone, Copy)]
pub struct PriceTime {
    price: BaseField,
    time: BaseField,
}

impl Default for PriceTime {
    fn default() -> Self {
        Self {
            price: BaseField::zero(),
            time: BaseField::zero(),
        }
    }
}

impl PartialEq for PriceTime {
    fn eq(&self, other: &Self) -> bool {
        self.price == other.price && self.time == other.time
    }
}

impl PartialOrd for PriceTime {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriceTime {
    fn cmp(&self, other: &Self) -> Ordering {
        // First comparision by price
        match self.price.cmp(&other.price) {
            Ordering::Equal => {
                // If prices are equal, comparision is by time
                self.time.cmp(&other.time)
            }
            ordering => ordering,
        }
    }
}

impl PriceTime {
    pub fn new(price: BaseField, time: BaseField) -> Self {
        Self { price, time }
    }

    pub fn price(&self) -> &BaseField {
        &self.price
    }

    pub fn time(&self) -> &BaseField {
        &self.time
    }

    pub fn into_inner(&self) -> (BaseField, BaseField) {
        (self.price, self.time)
    }

    pub fn from_inner((price, time): &(BaseField, BaseField)) -> Self {
        Self {
            price: *price,
            time: *time,
        }
    }

    pub fn from_felts(felts: [BaseField; 2]) -> Self {
        Self {
            price: felts[0],
            time: felts[1],
        }
    }

    pub fn to_felts(&self) -> [BaseField; 2] {
        [self.price, self.time]
    }

    pub fn is_zero(&self) -> bool {
        self.price.is_zero() && self.time.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use stwo_prover::core::fields::m31::M31;

    #[test]
    fn test_equality() {
        let pt1 = PriceTime::new(M31(10), M31(1));
        let pt2 = PriceTime::new(M31(41), M31(1));
        let pt3 = PriceTime::new(M31(10), M31(2));

        assert!(pt1 < pt2);
        assert!(pt1 < pt3);
        assert!(pt3 < pt2);
        assert_ne!(pt1, pt3);
    }

    #[test]
    fn test_ordering_by_price() {
        let pt1 = PriceTime::new(M31(10), M31(1));
        let pt2 = PriceTime::new(M31(20), M31(1));

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_ordering_by_time_when_prices_equal() {
        let pt1 = PriceTime::new(M31(10), M31(1));
        let pt2 = PriceTime::new(M31(41), M31(2)); // 41 ≡ 10 (mod 31)

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_btreemap_ordering() {
        let mut map = BTreeMap::new();

        // Insert in random order
        let pt3 = PriceTime::new(M31(10), M31(3));
        let pt1 = PriceTime::new(M31(10), M31(1));
        let pt2 = PriceTime::new(M31(10), M31(2));
        let pt4 = PriceTime::new(M31(5), M31(4));
        let pt5 = PriceTime::new(M31(15), M31(1));

        map.insert(pt3, "third");
        map.insert(pt1, "first");
        map.insert(pt2, "second");
        map.insert(pt4, "fourth");
        map.insert(pt5, "fifth");

        // Convert to vec for easier testing
        let entries: Vec<_> = map.into_iter().collect();

        // Check ordering
        assert_eq!(entries[0].0, pt4); // Lowest price (5) comes first
        assert_eq!(entries[1].0, pt1); // Price 10, earliest time
        assert_eq!(entries[2].0, pt2); // Price 10, middle time
        assert_eq!(entries[3].0, pt3); // Price 10, latest time
        assert_eq!(entries[4].0, pt5); // Highest price (15) comes last
    }
}

use std::array;

use crate::{
    error::GenericError,
    hash::hash_leaf,
    imt::Hash,
    types::{Price, Time, Volume},
};
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::BaseField;

#[derive(Clone)]
pub struct Leaf<F> {
    /// Determines if the leaf is active
    /// active leaf indicate whether the node contains an order eligible to be executed
    pub active: F,
    /// Unfilled Volume
    pub volume: Volume<F>,
    /// label determines the ordering in the IMT: Price Time Priority
    pub label: PriceTime<F>,
    /// next refers to the next leaf in the order book
    pub next: PriceTime<F>,
}

impl<F: Copy> Copy for Leaf<F> {}

impl<F: Copy + Default> Default for Leaf<F> {
    fn default() -> Self {
        Self {
            active: F::default(),
            volume: Volume::default(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }
}

impl Leaf<BaseField> {
    /// Return The first leaf of the IMT
    pub fn first() -> Self {
        Self {
            active: BaseField::one(),
            volume: Volume::default(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }

    /// Return inactive empty leaf
    pub fn empty() -> Self {
        Self {
            active: BaseField::zero(),
            volume: Volume::default(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }

    /// construct felts from leaf
    pub fn to_felts(&self) -> [BaseField; N_LEAF_FELTS] {
        let mut felts = array::from_fn(|_| BaseField::zero());
        felts[0] = self.active;
        felts[1..9].copy_from_slice(&self.volume.to_felts());
        felts[9..25].copy_from_slice(&self.label.to_felts());
        felts[25..41].copy_from_slice(&self.next.to_felts());
        felts
    }

    /// construct leaf from felts
    pub fn from_felts(felts: [BaseField; N_LEAF_FELTS]) -> Result<Self, GenericError> {
        let leaf = Self {
            active: felts[0],
            volume: Volume::try_from(&felts[1..9])?,
            label: PriceTime::try_from(&felts[9..25])?,
            next: PriceTime::try_from(&felts[25..41])?,
        };
        Ok(leaf)
    }

    /// poseidon hash of the leaf
    /// NOTE: This is a placeholder implementation
    /// NOTE: The Hasher is not implemented yet
    /// use with caution
    pub fn hash(&self) -> Hash<BaseField> {
        let felts = self.to_felts();
        let mut input_state = array::from_fn(|_| BaseField::zero());
        input_state[..16].clone_from_slice(&felts[..16]);
        hash_leaf(input_state)
    }
}

use std::cmp::Ordering;

use super::{N_LEAF_FELTS, N_U64_FELTS};

// Holds a price and a time, used as a key in the BTreeMap
#[derive(Debug, Clone)]
pub struct PriceTime<F> {
    price: Price<F>,
    time: Time<F>,
}

impl<F: Copy> Copy for PriceTime<F> {}
impl<F: Ord> Eq for PriceTime<F> {}

impl<F: Copy + Default> Default for PriceTime<F> {
    fn default() -> Self {
        PriceTime {
            price: Price::default(),
            time: Time::default(),
        }
    }
}

impl<F: Ord> PartialEq for PriceTime<F> {
    fn eq(&self, other: &Self) -> bool {
        self.price == other.price && self.time == other.time
    }
}

impl<F: Ord + Copy> PartialOrd for PriceTime<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Ord + Copy> Ord for PriceTime<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        // First comparison by price
        match self.price.cmp(&other.price) {
            Ordering::Equal => {
                // If prices are equal, comparison is by time
                self.time.cmp(&other.time)
            }
            ordering => ordering,
        }
    }
}

impl TryFrom<&[BaseField]> for PriceTime<BaseField> {
    type Error = GenericError;

    fn try_from(slice: &[BaseField]) -> Result<Self, Self::Error> {
        let price = Price::try_from(&slice[0..9])?;
        let time = Time::try_from(&slice[9..16])?;
        let price_time = PriceTime { price, time };
        Ok(price_time)
    }
}

impl PriceTime<BaseField> {
    pub fn new(price: u64, time: u64) -> Self {
        Self {
            price: Price::from_u64(price),
            time: Time::from_u64(time),
        }
    }

    pub fn price(&self) -> &Price<BaseField> {
        &self.price
    }

    pub fn time(&self) -> &Time<BaseField> {
        &self.time
    }

    pub fn into_inner(&self) -> (Price<BaseField>, Time<BaseField>) {
        (self.price, self.time)
    }

    pub fn from_inner((price, time): &(Price<BaseField>, Time<BaseField>)) -> Self {
        Self {
            price: *price,
            time: *time,
        }
    }

    pub fn from_felts(felts: [BaseField; 2 * N_U64_FELTS]) -> Result<Self, GenericError> {
        let price_time = Self {
            price: Price::try_from(&felts[0..8])?,
            time: Time::try_from(&felts[8..16])?,
        };
        Ok(price_time)
    }

    pub fn to_felts(&self) -> [BaseField; 2 * N_U64_FELTS] {
        let mut felts = [BaseField::default(); 2 * N_U64_FELTS];
        felts[0..8].copy_from_slice(&self.price.to_felts());
        felts[8..16].copy_from_slice(&self.time.to_felts());
        felts
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn test_equality() {
        let pt1 = PriceTime::new(100, 8);
        let pt2 = PriceTime::new(410, 8);
        let pt3 = PriceTime::new(100, 9);

        assert!(pt1 < pt2);
        assert!(pt1 < pt3);
        assert!(pt3 < pt2);
        assert_ne!(pt1, pt3);
    }

    #[test]
    fn test_ordering_by_price() {
        let pt1 = PriceTime::new(100, 8);
        let pt2 = PriceTime::new(200, 8);

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_ordering_by_time_when_prices_equal() {
        let pt1 = PriceTime::new(100, 8);
        let pt2 = PriceTime::new(410, 2); // 41 ≡ 10 (mod 31)

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_btreemap_ordering() {
        let mut map = BTreeMap::new();

        // Insert in random order
        let pt3 = PriceTime::new(100, 3);
        let pt1 = PriceTime::new(100, 1);
        let pt2 = PriceTime::new(100, 2);
        let pt4 = PriceTime::new(50, 4);
        let pt5 = PriceTime::new(150, 5);

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

use std::cmp::Ordering;
use std::{array, marker::PhantomData};

use super::PriceTimeFelts;
use super::{
    side::{Buy, OrderSide, Sell, Side},
    N_LEAF_FELTS, N_U64_FELTS,
};

use crate::{
    error::GenericError,
    hash::hash_leaf,
    imt::Hash,
    types::{Price, Time, Volume},
};
use num_traits::{One, Zero};
use stwo_constraint_framework::EvalAtRow;
use stwo_prover::prover::backend::simd::column::BaseColumn;
use stwo_prover::prover::backend::simd::m31::{PackedBaseField, LOG_N_LANES};
use stwo_prover::prover::backend::Column;
use stwo_prover::core::fields::m31::{BaseField, M31};

#[derive(Clone)]
pub struct Leaf<F, S> {
    /// Determines if the leaf is active
    /// active leaf indicate whether the node contains an order eligible to be executed
    pub active: F,
    /// Unfilled Volume
    pub volume: Volume<F>,
    /// label determines the ordering in the IMT: Price Time Priority
    pub label: PriceTime<F, S>,
    /// next refers to the next leaf in the order book
    pub next: PriceTime<F, S>,
}

impl<F: Copy, S: Clone> Copy for Leaf<F, S> {}

impl<F: Copy + Default, S> Default for Leaf<F, S> {
    fn default() -> Self {
        Self {
            active: F::default(),
            volume: Volume::default(),
            label: PriceTime::default(),
            next: PriceTime::default(),
        }
    }
}

pub struct LeafColumn;

impl LeafColumn {
    pub const ACTIVE: usize = 0;
    pub const VOLUME: usize = Self::ACTIVE + 1;
    pub const LABEL: usize = Self::VOLUME + N_U64_FELTS;
    pub const NEXT: usize = Self::LABEL + 2 * N_U64_FELTS;

    pub const PRICE: usize = Self::LABEL;
    pub const TIME: usize = Self::PRICE + N_U64_FELTS;
    pub const NEXT_PRICE: usize = Self::NEXT;
    pub const NEXT_TIME: usize = Self::NEXT_PRICE + N_U64_FELTS;
}

impl<S: OrderSide> Leaf<BaseField, S> {
    /// Return The first leaf of the IMT
    pub fn first() -> Self {
        Self {
            active: BaseField::one(),
            volume: Volume::default(),
            label: PriceTime::first(),
            next: PriceTime::last(),
        }
    }

    /// Return The first leaf of the IMT
    pub fn last() -> Self {
        Self {
            active: BaseField::one(),
            volume: Volume::default(),
            label: PriceTime::last(),
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

    /// constant function that returns empty leaf felts
    pub const fn empty_felts() -> [BaseField; N_LEAF_FELTS] {
        [M31(0); N_LEAF_FELTS]
    }

    /// active function returns boolean value of the active field
    pub fn is_active(&self) -> bool {
        self.active == BaseField::one()
    }

    /// returns price of the leaf
    pub fn price(&self) -> Price<BaseField> {
        self.label.price()
    }

    /// returns time of the leaf
    pub fn time(&self) -> Time<BaseField> {
        self.label.time()
    }

    /// returns the volume of the leaf
    pub fn volume(&self) -> Volume<BaseField> {
        self.volume
    }
}

impl<S: OrderSide> std::fmt::Debug for Leaf<BaseField, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Leaf Order")
            .field("volume", &self.volume.to_u64())
            .field("price", &self.price().to_u64())
            .field("time", &self.time().to_u64())
            .field("next_price", &self.next.price().to_u64())
            .field("next_time", &self.next.time().to_u64())
            .finish()
    }
}

impl<F: One + Zero + From<BaseField>, S: OrderSide> Leaf<F, S> {
    /// from_eval_felts returns a LessThanOp instance from a given EvalAtRow instance
    pub fn from_eval_felts<E: EvalAtRow>(eval: &mut E) -> Leaf<E::F, S> {
        let active = eval.next_trace_mask();
        let volume = array::from_fn(|_| eval.next_trace_mask());
        let price = array::from_fn(|_| eval.next_trace_mask());
        let time = array::from_fn(|_| eval.next_trace_mask());
        let next_price = array::from_fn(|_| eval.next_trace_mask());
        let next_time = array::from_fn(|_| eval.next_trace_mask());

        Leaf {
            active,
            volume: Volume::from_eval_felts(volume),
            label: PriceTime::from_eval_felts(price, time),
            next: PriceTime::from_eval_felts(next_price, next_time),
        }
    }

    /// first price time of the leaf
    pub fn first_price_time_felts() -> PriceTimeFelts<F> {
        let mut price_time = array::from_fn(|_| F::zero());
        match S::side() {
            Side::Buy => {
                for i in 0..N_U64_FELTS {
                    price_time[i] = F::from(M31(255))
                }
            }
            Side::Sell => {} // sell sides first price time is default/zeros
        }
        price_time
    }

    /// first price time cols of the first leaf
    pub fn first_price_time_cols(log_size: u32) -> [Vec<PackedBaseField>; 2 * N_U64_FELTS] {
        let mut price_time = array::from_fn(|_| BaseColumn::zeros(1 << log_size).data);
        match S::side() {
            Side::Buy => {
                for i in 0..N_U64_FELTS {
                    price_time[i] =
                        vec![PackedBaseField::broadcast(M31(255)); 1 << (log_size - LOG_N_LANES)]
                }
            }
            Side::Sell => {} // sell sides first price time is default/zeros
        }
        price_time
    }
}

pub type BuyLeaf<F> = Leaf<F, Buy>;
pub type SellLeaf<F> = Leaf<F, Sell>;

// Holds a price and a time, used as a key in the BTreeMap
#[derive(Clone)]
pub struct PriceTime<F, S> {
    price: Price<F>,
    time: Time<F>,
    _marker: PhantomData<S>,
}

impl<F: Copy, S: Clone> Copy for PriceTime<F, S> {}
impl<F: Ord, S: OrderSide> Eq for PriceTime<F, S> {}

impl<F: Copy + Default, S> Default for PriceTime<F, S> {
    fn default() -> Self {
        PriceTime {
            price: Price::default(),
            time: Time::default(),
            _marker: PhantomData,
        }
    }
}

impl<F: Ord, S: OrderSide> PartialEq for PriceTime<F, S> {
    fn eq(&self, other: &Self) -> bool {
        self.price == other.price && self.time == other.time
    }
}

impl<F: Ord + Copy, S: OrderSide> PartialOrd for PriceTime<F, S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Ord + Copy, S: OrderSide> Ord for PriceTime<F, S> {
    fn cmp(&self, other: &Self) -> Ordering {
        // First comparison by price
        match S::compare_prices(&self.price, &other.price) {
            Ordering::Equal => {
                // If prices are equal, comparison is by time
                self.time.cmp(&other.time)
            }
            ordering => ordering,
        }
    }
}

impl<S> TryFrom<&[BaseField]> for PriceTime<BaseField, S> {
    type Error = GenericError;

    fn try_from(slice: &[BaseField]) -> Result<Self, Self::Error> {
        let price = Price::try_from(&slice[0..9])?;
        let time = Time::try_from(&slice[9..16])?;
        let price_time = PriceTime {
            price,
            time,
            _marker: PhantomData,
        };
        Ok(price_time)
    }
}

impl<S: OrderSide> PriceTime<BaseField, S> {
    pub fn new(price: u64, time: u64) -> Self {
        Self {
            price: Price::from_u64(price),
            time: Time::from_u64(time),
            _marker: PhantomData,
        }
    }

    /// Return The first PriceTime of in the index map of the IMT
    pub fn first() -> Self {
        match S::side() {
            Side::Buy => Self {
                price: Price::from_u64(u64::MAX),
                time: Time::from_u64(0),
                _marker: PhantomData,
            },
            Side::Sell => Self {
                price: Price::from_u64(0),
                time: Time::from_u64(0),
                _marker: PhantomData,
            },
        }
    }

    /// Return The last PriceTime of in the index map of the IMT
    pub fn last() -> Self {
        match S::side() {
            Side::Buy => Self {
                price: Price::from_u64(0),
                time: Time::from_u64(0),
                _marker: PhantomData,
            },
            Side::Sell => Self {
                price: Price::from_u64(u64::MAX),
                time: Time::from_u64(0),
                _marker: PhantomData,
            },
        }
    }

    pub fn price(&self) -> Price<BaseField> {
        self.price
    }

    pub fn time(&self) -> Time<BaseField> {
        self.time
    }

    pub fn into_inner(&self) -> (Price<BaseField>, Time<BaseField>) {
        (self.price, self.time)
    }

    pub fn from_inner((price, time): &(Price<BaseField>, Time<BaseField>)) -> Self {
        Self {
            price: *price,
            time: *time,
            _marker: PhantomData,
        }
    }

    pub fn from_felts(felts: [BaseField; 2 * N_U64_FELTS]) -> Result<Self, GenericError> {
        let price_time = Self {
            price: Price::try_from(&felts[0..8])?,
            time: Time::try_from(&felts[8..16])?,
            _marker: PhantomData,
        };
        Ok(price_time)
    }

    pub fn to_felts(&self) -> [BaseField; 2 * N_U64_FELTS] {
        let mut felts = [BaseField::default(); 2 * N_U64_FELTS];
        felts[0..8].copy_from_slice(&self.price.to_felts());
        felts[8..16].copy_from_slice(&self.time.to_felts());
        felts
    }

    pub fn zero() -> Self {
        PriceTime::default()
    }
}

impl<F, S> PriceTime<F, S> {
    pub fn from_eval_felts(price: [F; N_U64_FELTS], time: [F; N_U64_FELTS]) -> Self {
        Self {
            price: Price::from_eval_felts(price),
            time: Time::from_eval_felts(time),
            _marker: PhantomData,
        }
    }
}

impl<S> std::fmt::Debug for PriceTime<BaseField, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PriceTime")
            .field("price", &self.price.to_u64())
            .field("time", &self.time.to_u64())
            .finish()
    }
}

// For sell orders, lower prices have higher priority.
pub type SellPriceTime<F> = PriceTime<F, Sell>;

// For buy orders, higher prices have higher priority.
pub type BuyPriceTime<F> = PriceTime<F, Buy>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn test_first_price_time() {
        let first_price_time = Leaf::<BaseField, Buy>::first_price_time_felts();
        let first_leaf = Leaf::<BaseField, Buy>::first();
        assert_eq!(first_price_time, first_leaf.label.to_felts());
        assert_eq!(first_leaf.time(), Time::from_u64(0)); // Time at first leaf is 0
        assert_eq!(first_leaf.price(), Price::from_u64(u64::MAX)); // buy side => price is decreasing order as priority decreases

        let first_price_time = Leaf::<BaseField, Sell>::first_price_time_felts();
        let first_leaf = Leaf::<BaseField, Sell>::first();
        assert_eq!(first_price_time, first_leaf.label.to_felts());
        assert_eq!(first_leaf.time(), Time::from_u64(0)); // Time at first leaf is 0
        assert_eq!(first_leaf.price(), Price::from_u64(0)); // sell side => price is increasing order as priority decreases
    }

    #[test]
    fn test_equality() {
        let pt1 = SellPriceTime::new(100, 8);
        let pt2 = SellPriceTime::new(410, 8);
        let pt3 = SellPriceTime::new(100, 9);

        assert!(pt1 < pt2); // 100 is better sell price than 410
        assert!(pt1 < pt3); // 100, 8 is better sell price than 100, 9 as time is earlier
        assert!(pt3 < pt2); // 100, 9 is better sell price than 410, 8 as price is lower
        assert_ne!(pt1, pt3); // 100, 8 is not equal to 100, 9
    }

    #[test]
    fn test_ordering_by_price() {
        let pt1 = SellPriceTime::new(100, 8);
        let pt2 = SellPriceTime::new(200, 8);

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_ordering_by_time_when_prices_equal() {
        let pt1 = SellPriceTime::new(100, 8);
        let pt2 = SellPriceTime::new(410, 2); // 41 ≡ 10 (mod 31)

        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_btreemap_ordering() {
        let mut map = BTreeMap::new();

        // Insert in random order
        let pt3 = SellPriceTime::new(100, 3);
        let pt1 = SellPriceTime::new(100, 1);
        let pt2 = SellPriceTime::new(100, 2);
        let pt4 = SellPriceTime::new(50, 4);
        let pt5 = SellPriceTime::new(150, 5);

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
    #[test]
    fn test_buy_price_time_equality() {
        let pt1 = BuyPriceTime::new(100, 8);
        let pt2 = BuyPriceTime::new(410, 8);
        let pt3 = BuyPriceTime::new(100, 9);

        assert_ne!(pt1, pt2);
        assert_ne!(pt1, pt3);
        assert_ne!(pt2, pt3);
    }

    #[test]
    fn test_buy_ordering_by_price() {
        let pt1 = BuyPriceTime::new(200, 8);
        let pt2 = BuyPriceTime::new(100, 8);

        // For buy orders, higher prices should come first
        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_buy_ordering_by_time_when_prices_equal() {
        let pt1 = BuyPriceTime::new(100, 8);
        let pt2 = BuyPriceTime::new(100, 10);

        // When prices are equal, earlier time should come first
        assert!(pt1 < pt2);
        assert!(pt2 > pt1);
    }

    #[test]
    fn test_buy_btreemap_ordering() {
        let mut map = BTreeMap::new();

        // Insert in random order
        let pt3 = BuyPriceTime::new(100, 3);
        let pt1 = BuyPriceTime::new(100, 1);
        let pt2 = BuyPriceTime::new(100, 2);
        let pt4 = BuyPriceTime::new(150, 4);
        let pt5 = BuyPriceTime::new(50, 5);

        map.insert(pt3, "third");
        map.insert(pt1, "first");
        map.insert(pt2, "second");
        map.insert(pt4, "fourth");
        map.insert(pt5, "fifth");

        // Convert to vec for easier testing
        let entries: Vec<_> = map.into_iter().collect();

        // Check ordering - for buy orders, highest price comes first
        assert_eq!(entries[0].0, pt4); // Highest price (150) comes first
        assert_eq!(entries[1].0, pt1); // Price 100, earliest time
        assert_eq!(entries[2].0, pt2); // Price 100, middle time
        assert_eq!(entries[3].0, pt3); // Price 100, latest time
        assert_eq!(entries[4].0, pt5); // Lowest price (50) comes last
    }

    #[test]
    fn test_buy_find_low() {
        let mut map = BTreeMap::new();

        // Insert in random order
        let pt0 = BuyPriceTime::new(u64::MAX, 0);
        let pt3 = BuyPriceTime::new(100, 3);
        let pt1 = BuyPriceTime::new(100, 1);
        let pt2 = BuyPriceTime::new(100, 2);
        let pt4 = BuyPriceTime::new(150, 4);
        let pt5 = BuyPriceTime::new(50, 5);

        map.insert(pt0, "zero");
        let low = map
            .range(..pt3)
            .next_back()
            .map(|(_, &index)| index)
            .unwrap();
        assert!(low == "zero");
        map.insert(pt3, "third");
        map.insert(pt1, "first");
        map.insert(pt2, "second");
        map.insert(pt4, "fourth");
        map.insert(pt5, "fifth");

        // Convert to vec for easier testing
        let entries: Vec<_> = map.into_iter().collect();

        // Check ordering - for buy orders, highest price comes first
        assert_eq!(entries[0].0, pt0); // 0th Entry
        assert_eq!(entries[1].0, pt4); // Highest price (150) comes first
        assert_eq!(entries[2].0, pt1); // Price 100, earliest time
        assert_eq!(entries[3].0, pt2); // Price 100, middle time
        assert_eq!(entries[4].0, pt3); // Price 100, latest time
        assert_eq!(entries[5].0, pt5); // Lowest price (50) comes last
    }
}

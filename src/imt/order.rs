use crate::{
    imt::N_ORDER_FELTS,
    types::{Price, Time, Volume},
};
use num_traits::One;
use stwo_prover::core::fields::m31::BaseField;

use super::{
    leaf::{Leaf, PriceTime},
    side::{Buy, OrderSide, Sell},
};

/// Order struct - generic in field BaseField
#[derive(Clone, Copy)]
pub struct Order<F, S> {
    /// volume of the order
    pub volume: Volume<F>,
    /// price of the order
    pub price_time: PriceTime<F, S>,
}

impl<S: OrderSide> Order<BaseField, S> {
    /// Creates a new Order.
    pub fn new(volume: u64, price: u64, time: u64) -> Self {
        Self {
            volume: Volume::from_u64(volume),
            price_time: PriceTime::new(price, time),
        }
    }
    /// converts the order to a leaf
    pub fn to_leaf(&self, next: &PriceTime<BaseField, S>) -> Leaf<BaseField, S> {
        Leaf {
            active: BaseField::one(),
            volume: self.volume,
            label: self.price_time,
            next: *next,
        }
    }

    /// converts the order to felts
    pub fn to_felts(&self) -> [BaseField; N_ORDER_FELTS] {
        let mut felts = [BaseField::default(); N_ORDER_FELTS];
        felts[0..8].copy_from_slice(&self.volume.to_felts());
        felts[8..24].copy_from_slice(&self.price_time.to_felts());
        felts
    }

    /// returns true if the order is invalid
    pub fn is_invalid(&self) -> bool {
        self.volume == Volume::zero()
            || self.price() == Price::zero()
            || self.time() == Time::zero()
    }

    pub fn price(&self) -> Price<BaseField> {
        self.price_time.price()
    }

    pub fn time(&self) -> Time<BaseField> {
        self.price_time.time()
    }

    pub fn volume(&self) -> Volume<BaseField> {
        self.volume
    }
}

impl Order<BaseField, Buy> {
    /// Creates a new Buy Order.
    pub fn new_buy(volume: u64, price: u64, time: u64) -> Self {
        Order::<BaseField, Buy>::new(volume, price, time)
    }
}

impl Order<BaseField, Sell> {
    /// Creates a new Sell Order.
    pub fn new_sell(volume: u64, price: u64, time: u64) -> Self {
        Order::<BaseField, Sell>::new(volume, price, time)
    }
}

impl<S: OrderSide> std::fmt::Debug for Order<BaseField, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Order")
            .field("volume", &self.volume.to_u64())
            .field("price", &self.price().to_u64())
            .field("time", &self.time().to_u64())
            .finish()
    }
}

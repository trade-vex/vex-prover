use crate::{imt::N_ORDER_FELTS, types::Volume};
use num_traits::One;
use stwo_prover::core::fields::m31::BaseField;

use super::{
    leaf::{Leaf, PriceTime},
    side::{Buy, OrderSide, Sell},
};

/// Order struct - generic in field BaseField
#[derive(Debug, Clone, Copy)]
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

    pub fn new_buy(volume: u64, price: u64, time: u64) -> Order<BaseField, Buy> {
        Order::<BaseField, Buy>::new(volume, price, time)
    }

    pub fn new_sell(volume: u64, price: u64, time: u64) -> Order<BaseField, Sell> {
        Order::<BaseField, Sell>::new(volume, price, time)
    }
}

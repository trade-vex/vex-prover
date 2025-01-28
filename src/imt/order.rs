use crate::{
    imt::{BaseField, N_ORDER_FELTS},
    types::{Price, Time, Volume},
};
use num_traits::One;

use super::leaf::{Leaf, PriceTime};

/// Order struct - generic in field BaseField
#[derive(Debug, Clone, Copy)]
pub struct Order {
    /// volume of the order
    pub volume: Volume<BaseField>,
    /// price of the order
    pub price_time: PriceTime,
}

impl Order {
    /// Creates a new Order.
    pub fn new(volume: Volume<BaseField>, price: Price<BaseField>, time: Time<BaseField>) -> Self {
        Self {
            volume,
            price_time: PriceTime::new(price, time),
        }
    }
}

impl Order {
    /// converts the order to a leaf
    pub fn to_leaf(&self, next: &PriceTime) -> Leaf {
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
}

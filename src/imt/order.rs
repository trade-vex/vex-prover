use crate::imt::BaseField;
use num_traits::One;

use super::leaf::{Leaf, PriceTime};

/// Order struct - generic in field BaseField
#[derive(Debug, Clone, Copy)]
pub struct Order {
    /// volume of the order
    pub volume: BaseField,
    /// price of the order
    pub price_time: PriceTime,
}

impl Order {
    /// Creates a new Order.
    pub fn new(volume: BaseField, price: BaseField, time: BaseField) -> Self {
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
}

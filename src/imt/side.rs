use std::fmt::Debug;

use crate::types::Price;

/// Type markers for Buy and Sell sides
#[derive(Debug, Clone, Copy)]
pub struct Buy;
#[derive(Debug, Clone, Copy)]
pub struct Sell;

/// IMT side marker
pub enum Side {
    Buy,
    Sell,
}

/// Trait for defining order comparison logic
pub trait OrderSide: Clone + Copy + Debug {
    /// Compare prices according to this side's priority rules
    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering;
    /// side marker
    fn side() -> Side;
}

impl OrderSide for Buy {
    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering {
        // For buy side, higher prices have higher priority (descending)
        b.cmp(a)
    }
    fn side() -> Side {
        Side::Buy
    }
}

impl OrderSide for Sell {
    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering {
        // For sell side, lower prices have higher priority (ascending)
        a.cmp(b)
    }
    fn side() -> Side {
        Side::Sell
    }
}

use crate::{executor::instruction::IMTOperation, types::Price};
use std::fmt::Debug;
use stwo_prover::core::fields::m31::BaseField;

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

/// Order side marker trait with compile-time constants
pub trait OrderSide: 'static + Copy + Send + Sync + Clone + Copy + Debug {
    /// Associated constant for side name
    const NAME: &'static str;
    /// Associated constant for side variant
    const SIDE: Side;
    /// Compare prices according to this side's priority rules
    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering;
    /// side marker
    fn side() -> Side {
        Self::SIDE
    }
    /// get op code based on the imt operation
    fn op_code(op: IMTOperation) -> BaseField;
    /// get the name of the side
    fn name() -> &'static str {
        match Self::side() {
            Side::Buy => "Buy",
            Side::Sell => "Sell",
        }
    }
}

impl OrderSide for Buy {
    const NAME: &'static str = "Buy";
    const SIDE: Side = Side::Buy;

    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering {
        // For buy side, higher prices have higher priority (descending)
        b.cmp(a)
    }
    fn op_code(op: IMTOperation) -> BaseField {
        match op {
            IMTOperation::Insertion => BaseField::from_u32_unchecked(0),
            IMTOperation::Deletion => BaseField::from_u32_unchecked(4),
            IMTOperation::Update => BaseField::from_u32_unchecked(2),
            IMTOperation::Match => BaseField::from_u32_unchecked(6),
            IMTOperation::PartialMatch => BaseField::from_u32_unchecked(8),
        }
    }
}

impl OrderSide for Sell {
    const NAME: &'static str = "Sell";
    const SIDE: Side = Side::Sell;
    fn compare_prices<F: Ord + Copy>(a: &Price<F>, b: &Price<F>) -> std::cmp::Ordering {
        // For sell side, lower prices have higher priority (ascending)
        a.cmp(b)
    }
    fn op_code(op: IMTOperation) -> BaseField {
        match op {
            IMTOperation::Insertion => BaseField::from_u32_unchecked(1),
            IMTOperation::Deletion => BaseField::from_u32_unchecked(5),
            IMTOperation::Update => BaseField::from_u32_unchecked(3),
            IMTOperation::Match => BaseField::from_u32_unchecked(7),
            IMTOperation::PartialMatch => BaseField::from_u32_unchecked(9),
        }
    }
}

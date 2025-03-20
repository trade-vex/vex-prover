use crate::{executor::instruction::IMTOperation, types::Price};
use num_traits::One;
use std::fmt::Debug;
use stwo_prover::core::fields::m31::BaseField;

/// Type markers for Buy and Sell sides
#[derive(Debug, Clone, Copy)]
pub struct Buy;
#[derive(Debug, Clone, Copy)]
pub struct Sell;

/// Type markers for Buy and Sell sides
#[derive(Debug, Clone, Copy)]
pub struct Aggressive;
#[derive(Debug, Clone, Copy)]
pub struct Passive;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchType {
    Aggressive,
    Passive,
}

/// Order match type marker trait with compile-time constants
pub trait OrderMatchType: 'static + Copy + Send + Sync + Clone + Copy + Debug {
    /// Associated constant for match type name
    const NAME: &'static str;
    /// Associated constant for match type variant
    /// Match Invariant is only checked for Aggressive Side
    /// The Match Elements are yielded for Aggressive Side and used for Passive Side
    const MATCHTYPE: MatchType;
    /// Indicates number of LessThan interaction columns
    const LESSTHANCOL: usize;
    /// get the name of the match type
    fn name() -> &'static str {
        match Self::MATCHTYPE {
            MatchType::Aggressive => "Aggressive",
            MatchType::Passive => "Passive",
        }
    }
    /// get the type of the match
    fn match_type() -> MatchType {
        Self::MATCHTYPE
    }
}

impl OrderMatchType for Aggressive {
    const NAME: &'static str = "Aggressive";
    const MATCHTYPE: MatchType = MatchType::Aggressive;
    const LESSTHANCOL: usize = 1;
}
impl OrderMatchType for Passive {
    const NAME: &'static str = "Passive";
    const MATCHTYPE: MatchType = MatchType::Passive;
    const LESSTHANCOL: usize = 0;
}

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
    /// get the complement opcode, i.e., the opcode for the other side
    fn complement_op_code(op: IMTOperation) -> BaseField {
        match Self::side() {
            Side::Buy => Self::op_code(op) + BaseField::one(),
            Side::Sell => Self::op_code(op) - BaseField::one(),
        }
    }
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
            IMTOperation::Deletion => BaseField::from_u32_unchecked(2),
            IMTOperation::Update => BaseField::from_u32_unchecked(4),
            IMTOperation::MatchAggressive => BaseField::from_u32_unchecked(6),
            IMTOperation::MatchPassive => BaseField::from_u32_unchecked(8),
            IMTOperation::PartialMatchAggressive => BaseField::from_u32_unchecked(10),
            IMTOperation::PartialMatchPassive => BaseField::from_u32_unchecked(12),
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
            IMTOperation::Deletion => BaseField::from_u32_unchecked(3),
            IMTOperation::Update => BaseField::from_u32_unchecked(5),
            IMTOperation::MatchAggressive => BaseField::from_u32_unchecked(7),
            IMTOperation::MatchPassive => BaseField::from_u32_unchecked(9),
            IMTOperation::PartialMatchAggressive => BaseField::from_u32_unchecked(11),
            IMTOperation::PartialMatchPassive => BaseField::from_u32_unchecked(13),
        }
    }
}

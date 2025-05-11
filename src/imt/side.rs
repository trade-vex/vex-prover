use std::fmt::Debug;

use stwo_prover::core::fields::m31::BaseField;

use crate::{executor::instruction::{IMTOperation, Opcode}, types::Price};

/// Type markers for Buy and Sell sides
#[derive(Debug, Clone, Copy)]
pub struct Buy;
#[derive(Debug, Clone, Copy)]
pub struct Sell;

/// Type markers for Match Types
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
pub trait OrderSide: 'static + Copy + Send + Sync + Clone + Debug {
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
        Self::NAME
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
            IMTOperation::Insertion => Opcode::InsertBuyOrder.to_field(),
            IMTOperation::Update => Opcode::UpdateBuyOrder.to_field(),
            IMTOperation::Deletion => Opcode::CancelBuyOrder.to_field(),
            IMTOperation::MatchAggressive => Opcode::MatchAggressiveBuy.to_field(),
            IMTOperation::MatchPassive => Opcode::MatchPassiveBuy.to_field(),
            IMTOperation::PartialMatchAggressive => Opcode::PartialMatchAggressiveBuy.to_field(),
            IMTOperation::PartialMatchPassive => Opcode::PartialMatchPassiveBuy.to_field(),
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
            IMTOperation::Insertion => Opcode::InsertSellOrder.to_field(),
            IMTOperation::Update => Opcode::UpdateSellOrder.to_field(),
            IMTOperation::Deletion => Opcode::CancelSellOrder.to_field(),
            IMTOperation::MatchAggressive => Opcode::MatchAggressiveSell.to_field(),
            IMTOperation::MatchPassive => Opcode::MatchPassiveSell.to_field(),
            IMTOperation::PartialMatchAggressive => Opcode::PartialMatchAggressiveSell.to_field(),
            IMTOperation::PartialMatchPassive => Opcode::PartialMatchPassiveSell.to_field(),
        }
    }
}

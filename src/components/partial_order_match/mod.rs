use std::marker::PhantomData;

use stwo_constraint_framework::FrameworkComponent;
use stwo_prover::core::fields::qm31::SECURE_EXTENSION_DEGREE;

use crate::{
    executor::instruction::N_INSTRUCTION_FELTS,
    imt::{
        side::{Aggressive, Buy, OrderMatchType, Passive, Sell},
        MERKLE_HEIGHT,
    },
};

use super::TraceSize;

mod constraints;
mod trace;

pub use constraints::PartialMatchEval;
pub use trace::{interaction_trace, preprocessed_trace, trace};

pub type BuyAgessivePartialMatchComponent = FrameworkComponent<PartialMatchEval<Buy, Aggressive>>;
pub type BuyPassivePartialMatchComponent = FrameworkComponent<PartialMatchEval<Buy, Passive>>;

pub type SellAggressivePartialMatchComponent =
    FrameworkComponent<PartialMatchEval<Sell, Aggressive>>;
pub type SellPassivePartialMatchComponent = FrameworkComponent<PartialMatchEval<Sell, Passive>>;

/// Match Column
/// Each row of the trace is a Instruction field elements.
/// The last field is a flag to indicate if the row is real or padded
#[derive(Debug, Clone)]
pub struct PartialMatchColumn<T> {
    /// marker for type
    _marker: PhantomData<T>,
}

impl<T: OrderMatchType> TraceSize for PartialMatchColumn<T> {
    /// is_first column
    const PREPROCESSED_COLS: usize = 1;
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    /// Interaction columns (batched for efficiency):
    ///   - T::LESSTHANCOL less_than columns (1 for Aggressive, 0 for Passive)
    ///   - 1 add elements column (filled_volume + remaining_volume, volume)
    ///   - 1 match elements column (price, volume)
    ///   - 1 leaf_batch column (batches 3 leaf hash operations via common denominator)
    ///   - MERKLE_HEIGHT merkle_batch columns (each batches 3 tree operations per level)
    ///   - 1 instruction column (final state)
    ///
    /// Batching details:
    ///   - 3 leaf hashes (low original, matched original, matched updated)
    ///     batched into 1 column using common denominator technique
    ///   - 3 merkle verifications per level * MERKLE_HEIGHT levels
    ///     batched into MERKLE_HEIGHT columns (one batch per level)
    ///
    /// Total Columns:
    ///   - Aggressive: 1 + 1 + 1 + 1 + MERKLE_HEIGHT + 1 = 1 + 1 + 1 + 1 + 20 + 1 = 25
    ///   - Passive: 0 + 1 + 1 + 1 + MERKLE_HEIGHT + 1 = 0 + 1 + 1 + 1 + 20 + 1 = 24
    const INTERACTION_COLS: usize =
        (T::LESSTHANCOL + MERKLE_HEIGHT + 4) * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
use stwo_constraint_framework::{assert_constraints_on_polys as assert_constraints, FrameworkEval};
mod tests {
    use std::{cell::RefCell, marker::PhantomData, rc::Rc};

    use constraints::PartialMatchEval;
    use rand::Rng;
    use stwo_prover::{
        core::{
            channel::Blake2sChannel, fields::m31::BaseField, pcs::TreeVec,
            poly::circle::CanonicCoset,
        },
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::{
            addition::AddElements, less_than::LessThanElements, order_match::MatchElements,
            poseidon::PoseidonElements,
        },
        executor::{
            instruction::InstructionElements,
            order_book::OrderBook,
            record::{ExecutionTrace, Instructions},
        },
        imt::{
            order::Order,
            side::{Buy, OrderSide},
        },
    };

    use super::*;

    fn evaluate_trace<S: OrderSide, T: OrderMatchType>(
        partial_matches: Instructions<BaseField>,
        poseidon_elements: &PoseidonElements,
        less_than_elements: &LessThanElements,
        match_elements: &MatchElements,
        instruction_elements: &InstructionElements,
        add_elements: &AddElements,
    ) {
        let log_size = (partial_matches.len() - 1).ilog2() + 1;
        let span = span!(Level::INFO, "Trace Generation", log_size).entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace::<S, T>(partial_matches);
        let (interaction_trace, interaction_claim) = interaction_trace::<S, T>(
            &trace,
            poseidon_elements,
            less_than_elements,
            instruction_elements,
            match_elements,
            add_elements,
        );
        span.exit();

        let _span = span!(Level::INFO, "Evaluating Constraints", log_size).entered();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: PartialMatchEval<S, T> = PartialMatchEval {
            less_than_elements: less_than_elements.clone(),
            poseidon_elements: poseidon_elements.clone(),
            match_elements: match_elements.clone(),
            instruction_elements: instruction_elements.clone(),
            add_elements: add_elements.clone(),
            _side: PhantomData,
            _type: PhantomData,
            claim,
        };

        // panics if the constraints are not satisfied
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(log_size),
            |eval| {
                component.evaluate(eval);
            },
            interaction_claim.claimed_sum,
        );
    }

    #[test_log::test]
    fn test_partial_match_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut order_book = OrderBook::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 1 << 7;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            // using volume as 100, because partial matching is not implemented
            let buy_order = Order::new(
                rng.gen_range(100000..10000000),
                rng.gen_range(1000000..=1000990),
                time,
            );
            let sell_order = Order::new(
                rng.gen_range(100000..10000000),
                rng.gen_range(1000000..=1000990),
                time,
            );
            order_book.place_buy_order(buy_order).unwrap();
            order_book.place_sell_order(sell_order).unwrap();
        }

        let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let poseidon_elements = PoseidonElements::draw(&mut channel);
        let less_than_elements = LessThanElements::draw(&mut channel);
        let match_elements = MatchElements::draw(&mut channel);
        let instruction_elements = InstructionElements::draw(&mut channel);
        let add_elements = AddElements::draw(&mut channel);

        // Aggressive Buy Trace Evaluation
        evaluate_trace::<Buy, Aggressive>(
            execution_trace.buy_aggressive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
            &add_elements,
        );

        // Passive Buy Trace Evaluation
        evaluate_trace::<Buy, Passive>(
            execution_trace.buy_passive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
            &add_elements,
        );

        evaluate_trace::<Sell, Aggressive>(
            execution_trace.sell_aggressive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
            &add_elements,
        );

        evaluate_trace::<Sell, Passive>(
            execution_trace.sell_passive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
            &add_elements,
        );
    }
}

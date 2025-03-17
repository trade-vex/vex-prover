use std::marker::PhantomData;

use stwo_prover::{
    constraint_framework::FrameworkComponent, core::fields::secure_column::SECURE_EXTENSION_DEGREE,
};

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
    /// number of poseidon hashes: 3 times for leaf hashes
    ///     - 1 for 0th leaf
    ///     - 1 for merkle_proof for matched leaf
    ///     - 1 for updated matched leaf (leaf.active = zero)
    /// 3*MERKLE_HEIGHT for merkle paths verification
    /// Total Poseidon Interactions: 3 + 3*MERKLE_HEIGHT
    /// Match Invariant: MAX(buy_imt) >= MIN(sell_imt) only in Aggressive Side
    /// Total Non Strict Less Than Interactions: 1
    /// When an Aggressive Match is made (price, volume) is yielded
    /// When an Passive Match is made (price, volume) is used
    /// 1 column for Match Elements (price, volume)
    /// 1 column for yielding the final result
    /// Total Columns: 3 + 3*MERKLE_HEIGHT + 3 + 1 + 1 = 4*MERKLE_HEIGHT + 9
    const INTERACTION_COLS: usize =
        ((3 * MERKLE_HEIGHT + 5) + T::LESSTHANCOL) * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, marker::PhantomData, rc::Rc};

    use constraints::PartialMatchEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{
            channel::Blake2sChannel, fields::m31::BaseField, pcs::TreeVec,
            poly::circle::CanonicCoset,
        },
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::{
            less_than::LessThanElements, order_match::MatchElements, poseidon::PoseidonElements,
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
        let n = 200;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            let buy_order = Order::new(rng.gen_range(1..100), rng.gen_range(100..=110), time);
            let sell_order = Order::new(rng.gen_range(1..100), rng.gen_range(100..=110), time);
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

        // Aggressive Buy Trace Evaluation
        evaluate_trace::<Buy, Aggressive>(
            execution_trace.buy_aggressive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
        );

        // Passive Buy Trace Evaluation
        evaluate_trace::<Buy, Passive>(
            execution_trace.buy_passive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
        );

        
        evaluate_trace::<Sell, Aggressive>(
            execution_trace.sell_aggressive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
        );

        evaluate_trace::<Sell, Passive>(
            execution_trace.sell_passive_partial_match,
            &poseidon_elements,
            &less_than_elements,
            &match_elements,
            &instruction_elements,
        );
    }
}

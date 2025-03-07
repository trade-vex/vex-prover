use stwo_prover::core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE};

use crate::executor::instruction::N_INSTRUCTION_FELTS;

use super::TraceSize;

mod constraints;
mod trace;

pub use trace::{interaction_trace, preprocessed_trace, trace};

// pub use trace::{interaction_trace, preprocessed_trace, trace};

/// Insertion Instructions
pub type Insertions = Vec<[BaseField; InsertionsColumn::MAIN_COLS]>;

/// Insertions Column
/// Each row of the trace is a InsertionsOp field elements arranged as per the `InsertionsColumn`
/// The last field is a flag to indicate if the row is real or padded
#[derive(Debug, Clone)]
pub struct InsertionsColumn;

impl TraceSize for InsertionsColumn {
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, marker::PhantomData, rc::Rc};

    use constraints::InsertionsEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::{
            less_than::{LessThanElements, StrictLessThanElements},
            poseidon::PoseidonElements,
        },
        executor::record::ExecutionTrace,
        imt::{
            order::Order,
            side::{Buy, OrderSide, Sell},
            BuyIMT, SellIMT,
        },
    };

    use super::*;

    fn evaluate_trace<S: OrderSide>(
        insertions: Insertions,
        poseidon_elements: &PoseidonElements,
        less_than_elements: &LessThanElements,
        strict_less_than_elements: &StrictLessThanElements,
    ) {
        let log_size = (insertions.len() - 1).ilog2() + 1;
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace::<S>(insertions);
        let (interaction_trace, interaction_claim) = interaction_trace::<S>(
            &trace,
            poseidon_elements,
            less_than_elements,
            strict_less_than_elements,
        );

        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: InsertionsEval<S> = InsertionsEval {
            less_than_elements: less_than_elements.clone(),
            poseidon_elements: poseidon_elements.clone(),
            strict_less_than_elements: strict_less_than_elements.clone(),
            _side: PhantomData,
            claim,
        };

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
    fn test_insertions_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut buy_imt = BuyIMT::new(Rc::clone(&record));
        let mut sell_imt = SellIMT::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 48;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            let buy_order = Order::new(rng.gen(), rng.gen(), time);
            let sell_order = Order::new(rng.gen(), rng.gen(), time);
            buy_imt.insert(buy_order).unwrap();
            sell_imt.insert(sell_order).unwrap();
        }

        let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let poseidon_elements = PoseidonElements::draw(&mut channel);
        let less_than_elements = LessThanElements::draw(&mut channel);
        let strict_less_than_elements = StrictLessThanElements::draw(&mut channel);

        // Evaluations Buy IMT
        evaluate_trace::<Buy>(
            execution_trace.buy_insert_order,
            &poseidon_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );

        // Evaluations Sell IMT
        evaluate_trace::<Sell>(
            execution_trace.sell_insert_order,
            &poseidon_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );
    }
}

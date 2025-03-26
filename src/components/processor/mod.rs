use stwo_prover::{
    constraint_framework::FrameworkComponent, core::fields::secure_column::SECURE_EXTENSION_DEGREE,
};

use crate::executor::instruction::N_INSTRUCTION_FELTS;

use super::TraceSize;

mod constraints;
mod trace;

pub use constraints::ProcessorEval;
pub use trace::{interaction_trace, preprocessed_trace, trace};

pub type ProcessorComponent = FrameworkComponent<ProcessorEval>;

/// Processor Column
/// Each row of the trace is an array of instruction field elements arranged as per the `InstructionColumn`
/// The last field is a flag to indicate if the row is real or padded
#[derive(Debug, Clone)]
pub struct ProcessorColumn;

impl TraceSize for ProcessorColumn {
    const PREPROCESSED_COLS: usize = 1;
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    /// 1st Column:"use initial state" and "yield final state" logups are batched
    /// 2nd Column: "use instruction elements"
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use constraints::ProcessorEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        executor::{
            instruction::InstructionElements, order_book::OrderBook, record::ExecutionTrace,
            state::StateElements,
        },
        imt::order::Order,
    };

    use super::*;

    #[test_log::test]
    fn test_processor_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut order_book = OrderBook::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 16;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            let buy_order = Order::new(rng.gen_range(1..=50), rng.gen_range(51..=100), time);
            let sell_order = Order::new(rng.gen_range(101..=150), rng.gen_range(151..=200), time);
            order_book.place_buy_order(buy_order).unwrap();
            order_book.place_sell_order(sell_order).unwrap();
        }

        let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let state_elements = StateElements::draw(&mut channel);
        let instruction_elements = InstructionElements::draw(&mut channel);

        let log_size = (execution_trace.instructions.len() - 1).ilog2() + 1;
        let span = span!(Level::INFO, "Trace Generation", log_size).entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace(execution_trace.instructions);
        let (interaction_trace, interaction_claim) =
            interaction_trace(&trace, &state_elements, &instruction_elements);
        span.exit();

        let _span = span!(Level::INFO, "Evaluating Constraints", log_size).entered();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: ProcessorEval = ProcessorEval {
            state_elements: state_elements.clone(),
            instruction_elements: instruction_elements.clone(),
            claim,
        };

        // panics if the constraints are not satisfied
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(log_size),
            |eval| {
                component.evaluate(eval);
            },
            (interaction_claim.claimed_sum, None),
        );
    }
}

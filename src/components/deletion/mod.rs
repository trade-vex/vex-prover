use super::TraceSize;
use crate::{executor::instruction::N_INSTRUCTION_FELTS, imt::MERKLE_HEIGHT};
use stwo_prover::core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE};

mod constraints;
mod trace;

pub use trace::{interaction_trace, preprocessed_trace, trace};

pub type Deletions = Vec<[BaseField; DeletionsColumn::MAIN_COLS]>;

#[derive(Debug, Clone)]
pub struct DeletionsColumn;

impl TraceSize for DeletionsColumn {
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    /// number of poseidon hashes: 4 times for leaf hashes
    ///     - 1 for target_merkle_proof
    ///     - 1 for parent_merkle_proof
    ///     - 1 for updated parent_leaf
    ///     - 1 for empty leaf
    ///  4*MERKLE_HEIGHT for merkle paths verification
    /// Total Poseidon Interactions: 4 + 4*MERKLE_HEIGHT
    /// Target and parent time checks => 1 equality check
    /// Target and parent price checks => 1 equality check
    /// Total Equality Interactions: 2
    /// 1 column for yielding the final result
    /// Total Columns: 4 + 4*MERKLE_HEIGHT + 2 + 1  = 4*MERKLE_HEIGHT + 9
    const INTERACTION_COLS: usize = (4 * MERKLE_HEIGHT + 9) * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, marker::PhantomData, rc::Rc};

    use constraints::DeletionsEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::poseidon::PoseidonElements,
        executor::{
            instruction::InstructionElements, order_book::OrderBook, record::ExecutionTrace,
        },
        imt::{
            order::Order,
            side::{Buy, OrderSide, Sell},
        },
    };

    use super::*;

    fn evaluate_trace<S: OrderSide>(
        mut deletions: Deletions,
        poseidon_elements: &PoseidonElements,
        instruction_elements: &InstructionElements,
    ) { 
        println!("Evaluating Deletions Trace");
        while deletions.len() < 16 {
            println!("hello");
            deletions.push(deletions[0]);
        }
        let mut log_size = (deletions.len() - 1).ilog2() + 1;
        let span = span!(Level::INFO, "Trace Generation", log_size).entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace::<S>(deletions);
        let (interaction_trace, interaction_claim) = interaction_trace::<S>(
            &trace, 
            poseidon_elements, 
            instruction_elements);
        span.exit();

        let _span = span!(Level::INFO, "Evaluating Constraints", log_size).entered();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: DeletionsEval<S> = DeletionsEval {
            poseidon_elements: poseidon_elements.clone(),
            instruction_elements: instruction_elements.clone(),
            claim,
            phantom: PhantomData,
        };
        println!("Evaluating Constraints");
        // panics if the constraints are not satisfied
        assert_constraints(
            &trace_polys,
            CanonicCoset::new(log_size),
            |eval| {
                component.evaluate(eval);
            },
            interaction_claim.claimed_sum,
        );
        println!("Constraints Satisfied");
    }

    #[test_log::test]
    fn test_deletions_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut order_book = OrderBook::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 4;

        // First, place some orders that we'll delete later
        let mut buy_order_pricetimes = Vec::new();
        let mut sell_order_pricetimes = Vec::new();
        
        for _ in 0..n {
            
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            
            // Create buy order
            let buy_price = rng.gen_range(1..=50);
            let buy_volume = rng.gen_range(51..=100);
            let buy_order = Order::new(buy_price, buy_volume, time);
            let buy_price_time = buy_order.price_time.clone(); // Store the price_time before placing
            
            // Create sell order
            let sell_price = rng.gen_range(101..=150);
            let sell_volume = rng.gen_range(151..=200);
            let sell_order = Order::new(sell_price, sell_volume, time);
            let sell_price_time = sell_order.price_time.clone(); // Store the price_time before placing
            
            // Place orders
            order_book.place_buy_order(buy_order).unwrap();
            order_book.place_sell_order(sell_order).unwrap();
            
            // Store identifiers for later cancellation
            buy_order_pricetimes.push(buy_price_time);
            sell_order_pricetimes.push(sell_price_time);
        }

        
        // Now delete some of the orders
        for i in 0..n/2 {
            time += rng.gen_range(1..=16);
            order_book.cancel_buy_order(buy_order_pricetimes[i]).unwrap();
            order_book.cancel_sell_order(sell_order_pricetimes[i]).unwrap();
        }

        let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let poseidon_elements = PoseidonElements::draw(&mut channel);
        let instruction_elements = InstructionElements::draw(&mut channel);

        // Evaluations Buy IMT
        evaluate_trace::<Buy>(
            execution_trace.buy_delete_order,
            &poseidon_elements,
            &instruction_elements,
        );

        // Evaluations Sell IMT
        evaluate_trace::<Sell>(
            execution_trace.sell_delete_order,
            &poseidon_elements,
            &instruction_elements,
        );
    }
}

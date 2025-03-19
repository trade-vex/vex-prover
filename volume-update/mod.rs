use stwo_prover::core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE};

use crate::{executor::instruction::N_INSTRUCTION_FELTS, imt::MERKLE_HEIGHT};

use super::TraceSize;

mod constraints;
mod trace;

pub use trace::{interaction_trace, preprocessed_trace, trace};

/// Volume Update Instructions
pub type VolumeUpdates = Vec<[BaseField; UpdateColumn::MAIN_COLS]>;

/// Volume Update Column
/// Each row of the trace is a VolumeUpdateOp field elements arranged as per the `VolumeUpdateColumn`
/// The last field is a flag to indicate if the row is real or padded
#[derive(Debug, Clone)]
pub struct UpdateColumn;

impl TraceSize for UpdateColumn {
    const MAIN_COLS: usize = N_INSTRUCTION_FELTS;
    /// number of poseidon hashes: 2 times for leaf hashes
    ///     - 1 for original leaf
    ///     - 1 for updated leaf
    /// 2*MERKLE_HEIGHT for merkle paths verification
    /// Total Poseidon Interactions: 2 + 2*MERKLE_HEIGHT
    /// No strict/non-strict less than checks required (unlike insertion)
    /// 1 column for yielding the final result
    /// Total Columns: 2 + 2*MERKLE_HEIGHT + 1 = 2*MERKLE_HEIGHT + 3
    const INTERACTION_COLS: usize = (2 * MERKLE_HEIGHT + 3) * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, marker::PhantomData, rc::Rc};

    use constraints::VolumeUpdateEval;
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace, preprocessed_trace, trace};
    use tracing::{span, Level};

    use crate::{
        components::{
            poseidon::PoseidonElements,
        },
        executor::{
            instruction::InstructionElements, order_book::OrderBook, record::ExecutionTrace,
        },
        imt::{
            order::Order,
            side::{Buy, OrderSide, Sell},
        },
        types::Volume,
    };

    use super::*;

    fn evaluate_trace<S: OrderSide>(
        volume_updates: VolumeUpdates,
        poseidon_elements: &PoseidonElements,
        instruction_elements: &InstructionElements,
    ) {
        let log_size = (volume_updates.len() - 1).ilog2() + 1;
        let span = span!(Level::INFO, "Trace Generation", log_size).entered();
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace::<S>(volume_updates);
        let (interaction_trace, interaction_claim) = interaction_trace::<S>(
            &trace,
            poseidon_elements,
            instruction_elements,
        );
        span.exit();

        let _span = span!(Level::INFO, "Evaluating Constraints", log_size).entered();
        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: VolumeUpdateEval<S> = VolumeUpdateEval {
            poseidon_elements: poseidon_elements.clone(),
            instruction_elements: instruction_elements.clone(),
            _side: PhantomData,
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
    fn test_volume_update_table() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut order_book = OrderBook::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        
        // First place orders
        let n = 1;
        let mut buy_orders = Vec::new();
        let mut sell_orders = Vec::new();
        
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            
            let buy_volume = rng.gen_range(1..=50);
            let buy_price = rng.gen_range(51..=100);
            let buy_order = Order::new(buy_volume, buy_price, time);
            
            let sell_volume = rng.gen_range(101..=150);
            let sell_price = rng.gen_range(151..=200);
            let sell_order = Order::new(sell_volume, sell_price, time);
            
            order_book.place_buy_order(buy_order.clone()).unwrap();
            order_book.place_sell_order(sell_order.clone()).unwrap();
            
            buy_orders.push(buy_order);
            sell_orders.push(sell_order);
        }
        
        // Now update volumes for some orders
        for i in 0..n/2 {
            let new_buy_volume = Volume::from([BaseField::fromrng.gen_range(51..=100); N_U64_LIMBS]);
            let new_sell_volume = Volume::from([BaseField::from(rng.gen_range(201..=250)); N_U64_LIMBS]);
            
            order_book.buy_volume_update(buy_orders[i].price_time, new_buy_volume).unwrap();
            order_book.sell_volume_update(sell_orders[i].price_time, new_sell_volume).unwrap();
        }

        let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let poseidon_elements = PoseidonElements::draw(&mut channel);
        let instruction_elements = InstructionElements::draw(&mut channel);

        // Evaluations Buy IMT volume updates
        evaluate_trace::<Buy>(
            execution_trace.buy_modify_order,
            &poseidon_elements,
            &instruction_elements,
        );

        // Evaluations Sell IMT volume updates
        evaluate_trace::<Sell>(
            execution_trace.sell_modify_order,
            &poseidon_elements,
            &instruction_elements,
        );
    }
}
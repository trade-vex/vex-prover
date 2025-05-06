use num_traits::{One, Zero};
use std::{cell::RefCell, rc::Rc};
use stwo_prover::core::fields::m31::BaseField;
use tracing::debug;

use crate::{
    executor::{
        flatten_single,
        instruction::{Opcode, N_INSTRUCTION_FELTS},
    },
    flatten,
    imt::{
        error::IMTError,
        leaf::PriceTime,
        order::Order,
        side::{Buy, Sell},
        BuyIMT, SellIMT,
    },
    types::Volume,
};

use super::{record::ExecutionTrace, state::State};

/// OrderBook Maintains Two IMTs for Buy and Sell Orders
/// It also maintains the state of the order book
/// The State consists of the current root hashes and the best price time for buy and sell orders
/// OrderBook Records the Execution Trace of the IMT Instructions every time there is a state transition
pub struct OrderBook {
    /// Buy IMT
    buy_imt: BuyIMT,
    /// Sell IMT
    sell_imt: SellIMT,
    /// Execution Trace
    trace: Rc<RefCell<ExecutionTrace<BaseField>>>,
    /// State of the Order Book
    state: State<BaseField>,
}

impl OrderBook {
    pub fn new(trace: Rc<RefCell<ExecutionTrace<BaseField>>>) -> Self {
        let buy_imt = BuyIMT::new(Rc::clone(&trace));
        let sell_imt = SellIMT::new(Rc::clone(&trace));
        let state = State::new(
            BaseField::zero(),
            buy_imt.root(),
            PriceTime::<BaseField, Buy>::last().to_felts(),
            sell_imt.root(),
            PriceTime::<BaseField, Sell>::last().to_felts(),
        );
        trace.borrow_mut().initial_state = state.to_felts();
        OrderBook {
            buy_imt,
            sell_imt,
            trace,
            state,
        }
    }

    /// Place a buy order in the order book
    /// Returns an error if the volume is zero, or the price_time is zero
    pub fn place_buy_order(&mut self, order: Order<BaseField, Buy>) -> Result<(), IMTError> {
        debug!("Placing buy order: {:?}", order);
        if order.is_invalid() {
            return Err(IMTError::InvalidOrder);
        }
        let initial_state = self.state;
        let proof = self.buy_imt.insert(order)?;
        debug_assert_eq!(initial_state.buy_root_hash, proof.initial_root);
        let mut final_state = initial_state;
        final_state.n += BaseField::one();
        final_state.buy_root_hash = self.buy_imt.root();
        final_state.buy_imt_priority = self.buy_imt.best_price_time();
        self.state = final_state;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root_hash,
            initial_state.buy_imt_priority,
            initial_state.sell_root_hash,
            initial_state.sell_imt_priority,
            Opcode::InsertBuyOrder.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            proof.low_merkle_updated_path,
            proof.low_index,
            proof.low_leaf.to_felts(),
            proof.inactive_proof,
            proof.inactive_path,
            proof.inactive_updated_path,
            proof.inactive_index,
            proof.leaf.to_felts(),
            final_state.n,
            final_state.buy_root_hash,
            final_state.buy_imt_priority,
            final_state.sell_root_hash,
            final_state.sell_imt_priority,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        self.match_buy(order)?;
        Ok(())
    }

    pub fn state(&self) -> State<BaseField> {
        self.state
    }

    /// Place a sell order in the order book
    /// Returns an error if the volume is zero, or the price_time is zero
    pub fn place_sell_order(&mut self, order: Order<BaseField, Sell>) -> Result<(), IMTError> {
        debug!("Placing sell order: {:?}", order);
        if order.is_invalid() {
            return Err(IMTError::InvalidOrder);
        }
        let initial_state = self.state;
        let proof = self.sell_imt.insert(order)?;
        debug_assert_eq!(initial_state.sell_root_hash, proof.initial_root);
        let mut final_state = initial_state;
        final_state.n += BaseField::one();
        final_state.sell_root_hash = self.sell_imt.root();
        final_state.sell_imt_priority = self.sell_imt.best_price_time();
        self.state = final_state;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root_hash,
            initial_state.buy_imt_priority,
            initial_state.sell_root_hash,
            initial_state.sell_imt_priority,
            Opcode::InsertSellOrder.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            proof.low_merkle_updated_path,
            proof.low_index,
            proof.low_leaf.to_felts(),
            proof.inactive_proof,
            proof.inactive_path,
            proof.inactive_updated_path,
            proof.inactive_index,
            proof.leaf.to_felts(),
            final_state.n,
            final_state.buy_root_hash,
            final_state.buy_imt_priority,
            final_state.sell_root_hash,
            final_state.sell_imt_priority,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        self.match_sell(order)?;
        Ok(())
    }
    /// Cancel a buy order in the order book
    /// Returns an error if the order doesn't exist or other IMT errors occur
    pub fn cancel_buy_order(&mut self, price_time: PriceTime<BaseField, Buy>) -> Result<(), IMTError> {
        debug!("Canceling buy order with price_time: {:?}", price_time);

        // Get the index of the order to cancel
        let index = self.buy_imt.find(&price_time)?;
        let initial_state = self.state;
        let proof = self.buy_imt.cancel_at_index(index)?;
        debug_assert_eq!(initial_state.buy_root_hash, proof.initial_root);
        
        let mut final_state = initial_state.clone();
        final_state.n += BaseField::one();
        final_state.buy_root_hash = self.buy_imt.root();
        final_state.buy_imt_priority = self.buy_imt.best_price_time();
        self.state = final_state;

        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root_hash,
            initial_state.buy_imt_priority,
            initial_state.sell_root_hash,
            initial_state.sell_imt_priority,
            Opcode::CancelBuyOrder.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            proof.low_merkle_updated_path,
            proof.low_index,
            proof.low_leaf.to_felts(),
            proof.cancel_leaf_proof,
            proof.cancel_leaf_path,
            proof.cancel_leaf_updated_path,
            proof.cancel_leaf_index,
            proof.cancel_leaf.to_felts(),
            final_state.n,
            final_state.buy_root_hash,
            final_state.buy_imt_priority,
            final_state.sell_root_hash,
            final_state.sell_imt_priority,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        Ok(())
    }

    /// Cancel a sell order in the order book
    /// Returns an error if the order doesn't exist or other IMT errors occur
    pub fn cancel_sell_order(&mut self, price_time: PriceTime<BaseField, Sell>) -> Result<(), IMTError> {
        debug!("Canceling sell order with price_time: {:?}", price_time);

        // Get the index of the order to cancel
        let index = self.sell_imt.find(&price_time)?;
        let initial_state = self.state;
        let proof = self.sell_imt.cancel_at_index(index)?;
        debug_assert_eq!(initial_state.sell_root_hash, proof.initial_root);
        
        let mut final_state = initial_state.clone();
        final_state.n += BaseField::one();
        final_state.sell_root_hash = self.sell_imt.root();
        final_state.sell_imt_priority = self.sell_imt.best_price_time();
        self.state = final_state;

        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root_hash,
            initial_state.buy_imt_priority,
            initial_state.sell_root_hash,
            initial_state.sell_imt_priority,
            Opcode::CancelSellOrder.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            proof.low_merkle_updated_path,
            proof.low_index,
            proof.low_leaf.to_felts(),
            proof.cancel_leaf_proof,
            proof.cancel_leaf_path,
            proof.cancel_leaf_updated_path,
            proof.cancel_leaf_index,
            proof.cancel_leaf.to_felts(),
            final_state.n,
            final_state.buy_root_hash,
            final_state.buy_imt_priority,
            final_state.sell_root_hash,
            final_state.sell_imt_priority,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        Ok(())
    }


    // @todo: state transition
    fn match_buy(&mut self, mut order: Order<BaseField, Buy>) -> Result<(), IMTError> {
        let price = order.price();
        // debug!("best sell price: {:?}", self.sell_imt.best_price());
        // debug!("best buy price: {:?}", self.buy_imt.best_price());
        while order.volume > Volume::zero() && price >= self.sell_imt.best_price() {
            debug!("best sell price: {:?}", self.sell_imt.best_price());
            let mut match_leaf = self.sell_imt.best_price_leaf();
            debug!("Match leaf: {:?}", match_leaf);
            let volume = if order.volume < match_leaf.volume {
                order.volume
            } else {
                match_leaf.volume
            };
            debug!("Filled volume: {:?}", volume.to_u64());
            order.volume -= volume;
            match_leaf.volume -= volume;

            if order.volume == Volume::zero() {
                self.buy_imt.match_order()?;
            } else {
                self.buy_imt.match_partially(volume)?;
            }

            if match_leaf.volume == Volume::zero() {
                self.sell_imt.match_order()?;
            } else {
                self.sell_imt.match_partially(volume)?;
            }
        }
        Ok(())
    }

    // @todo: state transition
    fn match_sell(&mut self, mut order: Order<BaseField, Sell>) -> Result<(), IMTError> {
        let price = order.price();
        // debug!("best buy price: {:?}", self.buy_imt.best_price());
        // debug!("best sell price: {:?}", self.sell_imt.best_price());
        while order.volume > Volume::zero() && price <= self.buy_imt.best_price() {
            debug!("best buy price: {:?}", self.buy_imt.best_price());
            let mut match_leaf = self.buy_imt.best_price_leaf();
            debug!("Match leaf: {:?}", match_leaf);
            let volume = if order.volume < match_leaf.volume {
                order.volume
            } else {
                match_leaf.volume
            };
            order.volume -= volume;
            match_leaf.volume -= volume;
            debug!("Filled volume: {:?}", volume.to_u64());
            if order.volume == Volume::zero() {
                self.sell_imt.match_order()?;
            } else {
                self.sell_imt.match_partially(volume)?;
            }
            debug!("Filled volume1: {:?}", volume.to_u64());
            if match_leaf.volume == Volume::zero() {
                self.buy_imt.match_order()?;
            } else {
                self.buy_imt.match_partially(volume)?;
            }
            debug!("Filled volume2: {:?}", volume.to_u64());
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use tracing::{span, Level};

    use super::*;
    use crate::{
        imt::{
            order::Order,
            side::{OrderSide, Side},
        },
        types::{Price, Time},
    };
    use crate::imt::leaf::Leaf;
    use crate::executor::instruction::InstructionColumn;

    #[test]
    fn test_place_buy_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        // Place a buy order and assert it was successful
        assert!(machine.place_buy_order(order).is_ok());
        // Check that the buy order was recorded in the trace
        assert!(trace.borrow().buy_insert_order.len() == 1);
    }

    #[test]
    fn test_place_sell_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        // Place a sell order and assert it was successful
        assert!(machine.place_sell_order(order).is_ok());
        // Check that the sell order was recorded in the trace
        assert!(trace.borrow().sell_insert_order.len() == 1);
    }

    #[test]
    fn test_match_buy_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let buy_order = Order::new(10, 100, 1);
        let sell_order = Order::new(10, 100, 2);
        // Place a sell order first
        assert!(machine.place_sell_order(sell_order).is_ok());
        // Then place a buy order that should match the sell order
        assert!(machine.place_buy_order(buy_order).is_ok());
        // Check that both orders were recorded in the trace
        assert!(trace.borrow().buy_insert_order.len() == 1);
        assert!(trace.borrow().sell_insert_order.len() == 1);
    }

    #[test]
    fn test_match_sell_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let buy_order = Order::new(10, 100, 1);
        let sell_order = Order::new(10, 100, 2);
        // Place a buy order first
        assert!(machine.place_buy_order(buy_order).is_ok());
        // Then place a sell order that should match the buy order
        assert!(machine.place_sell_order(sell_order).is_ok());
        // Check that both orders were recorded in the trace
        assert!(trace.borrow().buy_insert_order.len() == 1);
        assert!(trace.borrow().sell_insert_order.len() == 1);
    }

    #[test]
    fn test_basic_order_insertion() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));

        let buy_order = Order::new(10, 100, 1);
        let sell_order = Order::new(15, 110, 2);

        // Place buy and sell orders
        assert!(machine.place_buy_order(buy_order).is_ok());
        assert!(machine.place_sell_order(sell_order).is_ok());

        // Retrieve the leaves from the IMTs and check their properties
        let buy_leaf = machine.buy_imt.get_leaf_by_price_time(100, 1).unwrap();
        let sell_leaf = machine.sell_imt.get_leaf_by_price_time(110, 2).unwrap();

        // Ensure the leaves are active and have the correct volumes
        assert!(buy_leaf.is_active());
        assert!(sell_leaf.is_active());
        assert_eq!(buy_leaf.volume, Volume::from_u64(10));
        assert_eq!(sell_leaf.volume, Volume::from_u64(15));
    }

    #[test]
    fn test_exact_order_match() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));

        let buy_order = Order::new(10, 100, 1);
        let sell_order = Order::new(10, 100, 2);

        // Place sell and buy orders that should exactly match
        assert!(machine.place_sell_order(sell_order).is_ok());
        assert!(machine.place_buy_order(buy_order).is_ok());

        // Retrieve the leaves from the IMTs and check their properties
        let buy_leaf = machine.buy_imt.get_leaf_by_index(2).unwrap();
        let sell_leaf = machine.sell_imt.get_leaf_by_index(2).unwrap();

        // Ensure the leaves are inactive after the match
        assert!(!buy_leaf.is_active());
        assert!(!sell_leaf.is_active());
    }

    #[test]
    fn test_partial_order_match() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));

        let buy_order = Order::new(15, 100, 1);
        let sell_order = Order::new(10, 100, 2);

        // Place sell and buy orders that should partially match
        assert!(machine.place_sell_order(sell_order).is_ok());
        assert!(machine.place_buy_order(buy_order).is_ok());

        // Retrieve the leaves from the IMTs and check their properties
        let buy_leaf = machine.buy_imt.get_leaf_by_index(2).unwrap();
        let sell_leaf = machine.sell_imt.get_leaf_by_index(2).unwrap();

        // Ensure the sell leaf is inactive and the buy leaf is active with remaining volume
        assert!(!sell_leaf.is_active());
        assert!(buy_leaf.is_active());
        assert_eq!(buy_leaf.volume, Volume::from_u64(5)); // Remaining volume
    }

    #[test]
    fn test_price_time_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));

        let buy1 = Order::new(10, 100, 1); // Lower timestamp
        let buy2 = Order::new(10, 100, 2); // Higher timestamp
        let buy3 = Order::new(10, 110, 3); // Higher price

        // Place buy orders with different prices and timestamps
        assert!(machine.place_buy_order(buy1).is_ok());
        assert!(machine.place_buy_order(buy2).is_ok());
        assert!(machine.place_buy_order(buy3).is_ok());

        // Check that the highest price order is prioritized
        assert_eq!(machine.buy_imt.best_price(), Price::from_u64(110)); // Highest price wins
        assert_eq!(
            machine.buy_imt.best_price_leaf().label.time(),
            Time::from_u64(3)
        );
    }

    // currently the orders are places such that they are not matched
    // this test is to check if the orders are inserted correctly
    // this will be updated once the matching state updates are implemented
    fn generate_random_order<S: OrderSide>(time: u64, base_price: u64) -> Order<BaseField, S> {
        let mut rng = rand::thread_rng();
        let price = match S::side() {
            Side::Buy => rng.gen_range(1..=50),
            Side::Sell => rng.gen_range(101..=150),
        };
        let volume = rng.gen_range(1..100);
        Order::new(volume, base_price + price, time)
    }

    #[test_log::test]
    fn test_large_order_simulation() {
        let _span = span!(Level::INFO, "Order Simulation").entered();
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let mut time = 1;
        let base_price = 500; // Centralized price range for close matches

        for i in 0..10000 {
            let buy_order = generate_random_order::<Buy>(time, base_price);
            let sell_order = generate_random_order::<Sell>(time, base_price);
            // Place random buy and sell orders
            assert!(machine
                .place_buy_order(buy_order)
                .map_err(|e| println!("Error placing buy order: {:?}", e))
                .is_ok());
            assert!(machine
                .place_sell_order(sell_order)
                .map_err(|e| println!("Error placing sell order: {:?}", e))
                .is_ok());
            // Retrieve the leaves from the IMTs and check their properties
            let buy_leaf = machine.buy_imt.get_leaf_by_index(i + 2).unwrap();
            let sell_leaf = machine.sell_imt.get_leaf_by_index(i + 2).unwrap();

            // Assert leaf has been inserted properly
            assert_eq!(buy_leaf.price(), buy_order.price());
            assert_eq!(sell_leaf.price(), sell_order.price());
            assert_eq!(buy_leaf.time(), buy_order.time());
            assert_eq!(sell_leaf.time(), sell_order.time());

            time += 2;
        }
    }
    fn get_buy_leaf_safely(machine: &OrderBook, pt: PriceTime<BaseField, Buy>) -> Result<Leaf<BaseField, Buy>, String> {
        machine.buy_imt.get_leaf_by_price_time(pt.price().to_u64(), pt.time().to_u64())
            .map_err(|e| format!("Failed to get buy leaf for {:?}: {:?}", pt, e))
    }

    fn get_sell_leaf_safely(machine: &OrderBook, pt: PriceTime<BaseField, Sell>) -> Result<Leaf<BaseField, Sell>, String> {
        machine.sell_imt.get_leaf_by_price_time(pt.price().to_u64(), pt.time().to_u64())
             .map_err(|e| format!("Failed to get sell leaf for {:?}: {:?}", pt, e))
    }

    #[test]
    fn test_cancel_buy_order_simple() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time; // Get PriceTime

        // Place the order
        assert!(machine.place_buy_order(order.clone()).is_ok(), "Failed to place buy order");

        // *** Check leaf exists AFTER insertion ***
        let leaf_after_insert = get_buy_leaf_safely(&machine, pt)
            .expect("Leaf MUST exist immediately after insertion");
        assert!(leaf_after_insert.is_active(), "Leaf is inactive immediately after insertion");


        let initial_state_before_cancel = machine.state.clone();
        let initial_root = machine.buy_imt.root();
        assert_eq!(trace.borrow().buy_insert_order.len(), 1);
        assert_eq!(trace.borrow().buy_delete_order.len(), 0);

        // Cancel the order
        let cancel_result = machine.cancel_buy_order(pt);
        // *** Check cancel result explicitly ***
        assert!(cancel_result.is_ok(), "cancel_buy_order failed: {:?}", cancel_result.err());


        let final_state = machine.state.clone();

        // Check trace
        assert_eq!(trace.borrow().buy_insert_order.len(), 1);
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);

        // Check state transition counter 'n'
        assert_eq!(final_state.n, initial_state_before_cancel.n + BaseField::one());

        // Check root hash changed
        assert_ne!(final_state.buy_root_hash, initial_root, "Root hash did not change");

        // Check if priority updated
        assert_eq!(final_state.buy_imt_priority, PriceTime::<BaseField, Buy>::last().to_felts(), "Priority not reset");


        // Verify the correct opcode was added
        let binding = trace.borrow();
        let last_instruction = binding.instructions.last().expect("Instruction trace empty");
        assert_eq!(last_instruction[InstructionColumn::OPCODE], Opcode::CancelBuyOrder.to_field());
    }

    #[test]
    fn test_cancel_sell_order_simple() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time; // Get PriceTime

        // Place the order
        assert!(machine.place_sell_order(order.clone()).is_ok(), "Failed to place sell order");

        // *** Check leaf exists AFTER insertion ***
         let leaf_after_insert = get_sell_leaf_safely(&machine, pt)
             .expect("Leaf MUST exist immediately after insertion");
         assert!(leaf_after_insert.is_active(), "Leaf is inactive immediately after insertion");


        let initial_state_before_cancel = machine.state.clone();
        let initial_root = machine.sell_imt.root();
        assert_eq!(trace.borrow().sell_insert_order.len(), 1);
        assert_eq!(trace.borrow().sell_delete_order.len(), 0);

        // Cancel the order
        let cancel_result = machine.cancel_sell_order(pt);
        // *** Check cancel result explicitly ***
        assert!(cancel_result.is_ok(), "cancel_sell_order failed: {:?}", cancel_result.err());


        let final_state = machine.state.clone();

        // Check trace
        assert_eq!(trace.borrow().sell_insert_order.len(), 1);
        assert_eq!(trace.borrow().sell_delete_order.len(), 1);

        // Check state transition counter 'n'
        assert_eq!(final_state.n, initial_state_before_cancel.n + BaseField::one());

        // Check root hash changed
        assert_ne!(final_state.sell_root_hash, initial_root, "Root hash did not change");

        // Check if priority updated
        assert_eq!(final_state.sell_imt_priority, PriceTime::<BaseField, Sell>::last().to_felts(), "Priority not reset");


        // Verify the correct opcode was added
        let binding = trace.borrow();
        let last_instruction = binding.instructions.last().expect("Instruction trace empty");
        assert_eq!(last_instruction[InstructionColumn::OPCODE], Opcode::CancelSellOrder.to_field());
    }


    #[test]
    fn test_cancel_buy_order_updates_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Lower priority
        let order2 = Order::new(5, 110, 2);  // Highest priority
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_buy_order(order1.clone()).is_ok());
        assert!(machine.place_buy_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert = get_buy_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert = get_buy_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");


        // Verify initial priority is order2
        assert_eq!(machine.state.buy_imt_priority, pt2.to_felts());

        // Cancel the highest priority order (order2)
        let cancel_result = machine.cancel_buy_order(pt2);
        assert!(cancel_result.is_ok(), "cancel_buy_order failed for pt2: {:?}", cancel_result.err());


        // Verify priority updated to order1
        assert_eq!(machine.state.buy_imt_priority, pt1.to_felts());

        // Verify leaves state
        let leaf1 = get_buy_leaf_safely(&machine, pt1).expect("Leaf 1 should still exist after cancelling leaf 2");
        assert!(leaf1.is_active());
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);
    }

     #[test]
    fn test_cancel_sell_order_updates_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Higher priority (lower price)
        let order2 = Order::new(5, 110, 2);  // Lower priority
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_sell_order(order1.clone()).is_ok());
        assert!(machine.place_sell_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert = get_sell_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert = get_sell_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order1
        assert_eq!(machine.state.sell_imt_priority, pt1.to_felts());

        // Cancel the highest priority order (order1)
        let cancel_result = machine.cancel_sell_order(pt1);
        assert!(cancel_result.is_ok(), "cancel_sell_order failed for pt1: {:?}", cancel_result.err());


        // Verify priority updated to order2
        assert_eq!(machine.state.sell_imt_priority, pt2.to_felts());

        // Verify leaves state
        let leaf2 = get_sell_leaf_safely(&machine, pt2).expect("Leaf 2 should still exist after cancelling leaf 1");
        assert!(leaf2.is_active());
        assert_eq!(trace.borrow().sell_delete_order.len(), 1);
    }


    #[test]
    fn test_cancel_buy_order_does_not_update_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Lower priority - to be cancelled
        let order2 = Order::new(5, 110, 2);  // Highest priority - remains
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_buy_order(order1.clone()).is_ok());
        assert!(machine.place_buy_order(order2.clone()).is_ok());

         // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert = get_buy_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert = get_buy_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order2
        assert_eq!(machine.state.buy_imt_priority, pt2.to_felts());
        let initial_priority = machine.state.buy_imt_priority.clone();

        // Cancel the lower priority order (order1)
        let cancel_result = machine.cancel_buy_order(pt1);
        assert!(cancel_result.is_ok(), "cancel_buy_order failed for pt1: {:?}", cancel_result.err());


        // Verify priority did NOT change
        assert_eq!(machine.state.buy_imt_priority, initial_priority);
        assert_eq!(machine.state.buy_imt_priority, pt2.to_felts()); // Still order2

        // Verify leaves state
        let leaf2 = get_buy_leaf_safely(&machine, pt2).expect("Leaf 2 should still exist after cancelling leaf 1");
        assert!(leaf2.is_active());
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);
    }

    #[test]
    fn test_cancel_sell_order_does_not_update_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Highest priority - remains
        let order2 = Order::new(5, 110, 2);  // Lower priority - to be cancelled
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_sell_order(order1.clone()).is_ok());
        assert!(machine.place_sell_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert = get_sell_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert = get_sell_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order1
        assert_eq!(machine.state.sell_imt_priority, pt1.to_felts());
        let initial_priority = machine.state.sell_imt_priority.clone();

        // Cancel the lower priority order (order2)
        let cancel_result = machine.cancel_sell_order(pt2);
        assert!(cancel_result.is_ok(), "cancel_sell_order failed for pt2: {:?}", cancel_result.err());


        // Verify priority did NOT change
        assert_eq!(machine.state.sell_imt_priority, initial_priority);
        assert_eq!(machine.state.sell_imt_priority, pt1.to_felts()); // Still order1

        // Verify leaves state
        let leaf1 = get_sell_leaf_safely(&machine, pt1).expect("Leaf 1 should still exist after cancelling leaf 2");
        assert!(leaf1.is_active());
        assert_eq!(trace.borrow().sell_delete_order.len(), 1);
    }

    #[test]
    fn test_cancel_non_existent_buy_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time;
        let non_existent_pt = PriceTime::<BaseField, Buy>::new(999, 999);

        // Place an order
        assert!(machine.place_buy_order(order.clone()).is_ok());
        // Check it exists
        let _leaf_after_insert = get_buy_leaf_safely(&machine, pt).expect("Leaf MUST exist after insertion");

        let initial_state = machine.state.clone();
        let trace_len_before = trace.borrow().instructions.len();

        // Attempt to cancel a non-existent order
        let result = machine.cancel_buy_order(non_existent_pt);
        assert!(result.is_err(), "Cancellation of non-existent order should fail");
        // Optionally check the specific error type if IMTError exposes it
        // assert!(matches!(result.unwrap_err(), IMTError::LeafNotFound));


        // Verify state hasn't changed
        assert_eq!(machine.state, initial_state);

        // Verify no cancel instruction was added
        assert_eq!(trace.borrow().buy_delete_order.len(), 0);
        assert_eq!(trace.borrow().instructions.len(), trace_len_before);
    }

     #[test]
    fn test_cancel_non_existent_sell_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
         let pt = order.price_time;
        let non_existent_pt = PriceTime::<BaseField, Sell>::new(999, 999);

        // Place an order
        assert!(machine.place_sell_order(order.clone()).is_ok());
        // Check it exists
        let _leaf_after_insert = get_sell_leaf_safely(&machine, pt).expect("Leaf MUST exist after insertion");


        let initial_state = machine.state.clone();
        let trace_len_before = trace.borrow().instructions.len();

        // Attempt to cancel a non-existent order
        let result = machine.cancel_sell_order(non_existent_pt);
        assert!(result.is_err(), "Cancellation of non-existent order should fail");
        // assert!(matches!(result.unwrap_err(), IMTError::LeafNotFound));


        // Verify state hasn't changed
        assert_eq!(machine.state, initial_state);

        // Verify no cancel instruction was added
        assert_eq!(trace.borrow().sell_delete_order.len(), 0);
        assert_eq!(trace.borrow().instructions.len(), trace_len_before);
    }

     #[test]
    fn test_cancel_already_inactive_buy_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time;

        // Place and immediately cancel the order
        assert!(machine.place_buy_order(order.clone()).is_ok());
         let cancel1_result = machine.cancel_buy_order(pt);
         assert!(cancel1_result.is_ok(), "First cancel failed: {:?}", cancel1_result.err());

        let state_after_first_cancel = machine.state.clone();
        let trace_len_after_first_cancel = trace.borrow().instructions.len();

        // Attempt to cancel the already cancelled (inactive) order again
        let cancel2_result = machine.cancel_buy_order(pt);
        assert!(cancel2_result.is_err(), "Second cancellation of same order should fail");
        // Check specific error if possible, e.g., CannotCancelInactive
        // assert!(matches!(cancel2_result.unwrap_err(), IMTError::CannotCancelInactive));


        // Verify state hasn't changed since the first cancel
        assert_eq!(machine.state, state_after_first_cancel);

        // Verify no *additional* cancel instruction was added
        assert_eq!(trace.borrow().buy_delete_order.len(), 1); // Still 1 cancel
        assert_eq!(trace.borrow().instructions.len(), trace_len_after_first_cancel);
    }

    #[test]
    fn test_cancel_already_inactive_sell_order() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time;

        // Place and immediately cancel the order
        assert!(machine.place_sell_order(order.clone()).is_ok());
         let cancel1_result = machine.cancel_sell_order(pt);
         assert!(cancel1_result.is_ok(), "First cancel failed: {:?}", cancel1_result.err());


        let state_after_first_cancel = machine.state.clone();
        let trace_len_after_first_cancel = trace.borrow().instructions.len();

        // Attempt to cancel the already cancelled (inactive) order again
        let cancel2_result = machine.cancel_sell_order(pt);
        assert!(cancel2_result.is_err(), "Second cancellation of same order should fail");
        // assert!(matches!(cancel2_result.unwrap_err(), IMTError::CannotCancelInactive));


        // Verify state hasn't changed since the first cancel
        assert_eq!(machine.state, state_after_first_cancel);

        // Verify no *additional* cancel instruction was added
        assert_eq!(trace.borrow().sell_delete_order.len(), 1); // Still 1 cancel
        assert_eq!(trace.borrow().instructions.len(), trace_len_after_first_cancel);
    }
    
}

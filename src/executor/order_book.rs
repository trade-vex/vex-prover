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
        side::{Buy, OrderSide, Sell, Side},
        BuyIMT, IndexBits, MatchProof, MerklePath, PartialMatchProof, SellIMT, N_LEAF_FELTS,
        N_U64_FELTS,
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
            PriceTime::<BaseField, Buy>::last().price().to_felts(),
            sell_imt.root(),
            PriceTime::<BaseField, Sell>::last().price().to_felts(),
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
        debug_assert_eq!(initial_state.buy_root, proof.initial_root);
        let mut final_state = initial_state;
        final_state.n += BaseField::one();
        final_state.buy_root = self.buy_imt.root();
        final_state.best_buy_price = self.buy_imt.best_price_felts();
        self.state = final_state;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
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
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
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
        debug_assert_eq!(initial_state.sell_root, proof.initial_root);
        let mut final_state = initial_state;
        final_state.n += BaseField::one();
        final_state.sell_root = self.sell_imt.root();
        final_state.best_sell_price = self.sell_imt.best_price_felts();
        self.state = final_state;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
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
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        self.match_sell(order)?;
        Ok(())
    }
    /// Cancel a buy order in the order book
    /// Returns an error if the order doesn't exist or other IMT errors occur
    pub fn cancel_buy_order(
        &mut self,
        price_time: PriceTime<BaseField, Buy>,
    ) -> Result<(), IMTError> {
        debug!("Canceling buy order with price_time: {:?}", price_time);

        // Get the index of the order to cancel
        let index = self.buy_imt.find(&price_time)?;
        let initial_state = self.state;
        let proof = self.buy_imt.cancel_at_index(index)?;
        debug_assert_eq!(initial_state.buy_root, proof.initial_root);

        let mut final_state = initial_state.clone();
        final_state.n += BaseField::one();
        final_state.buy_root = self.buy_imt.root();
        final_state.best_buy_price = self.buy_imt.best_price().to_felts();
        self.state = final_state;

        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
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
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        Ok(())
    }

    /// Cancel a sell order in the order book
    /// Returns an error if the order doesn't exist or other IMT errors occur
    pub fn cancel_sell_order(
        &mut self,
        price_time: PriceTime<BaseField, Sell>,
    ) -> Result<(), IMTError> {
        debug!("Canceling sell order with price_time: {:?}", price_time);

        // Get the index of the order to cancel
        let index = self.sell_imt.find(&price_time)?;
        let initial_state = self.state;
        let proof = self.sell_imt.cancel_at_index(index)?;
        debug_assert_eq!(initial_state.sell_root, proof.initial_root);

        let mut final_state = initial_state.clone();
        final_state.n += BaseField::one();
        final_state.sell_root = self.sell_imt.root();
        final_state.best_sell_price = self.sell_imt.best_price().to_felts();
        self.state = final_state;

        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
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
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        Ok(())
    }

    fn match_buy(&mut self, mut order: Order<BaseField, Buy>) -> Result<(), IMTError> {
        let price = order.price();
        // debug!("best sell price: {:?}", self.sell_imt.best_price());
        // debug!("best buy price: {:?}", self.buy_imt.best_price());
        while order.volume > Volume::zero() && price >= self.sell_imt.best_price() {
            let mut match_leaf = self.sell_imt.best_price_leaf();
            let volume = if order.volume < match_leaf.volume {
                order.volume
            } else {
                match_leaf.volume
            };
            order.volume -= volume;
            match_leaf.volume -= volume;
            let initial_state = self.state;
            // buy is aggressive here
            // additional checks for the invariant
            // best(buy) >= best(sell)
            self.trace
                .borrow_mut()
                .add_less_than_event(match_leaf.price().to_felts(), order.price().to_felts())?;
            if order.volume == Volume::zero() {
                let proof = self.buy_imt.match_order()?;
                self.finalize_match(proof, true)?;
            } else {
                let proof = self.buy_imt.match_partially(volume)?;
                assert_eq!(initial_state.buy_root, proof.initial_root);
                self.finalize_partial_match(proof, true)?;
            }

            let initial_state = self.state;
            if match_leaf.volume == Volume::zero() {
                let proof = self.sell_imt.match_order()?;
                assert_eq!(initial_state.sell_root, proof.initial_root);
                self.finalize_match(proof, false)?;
            } else {
                let proof = self.sell_imt.match_partially(volume)?;
                assert_eq!(initial_state.sell_root, proof.initial_root);
                self.finalize_partial_match(proof, false)?;
            }
        }
        Ok(())
    }

    fn match_sell(&mut self, mut order: Order<BaseField, Sell>) -> Result<(), IMTError> {
        let price = order.price();
        // debug!("best buy price: {:?}", self.buy_imt.best_price());
        // debug!("best sell price: {:?}", self.sell_imt.best_price());
        while order.volume > Volume::zero() && price <= self.buy_imt.best_price() {
            let mut match_leaf = self.buy_imt.best_price_leaf();
            let volume = if order.volume < match_leaf.volume {
                order.volume
            } else {
                match_leaf.volume
            };
            order.volume -= volume;
            match_leaf.volume -= volume;

            self.trace
                .borrow_mut()
                .add_less_than_event(order.price().to_felts(), match_leaf.price().to_felts())?;
            if order.volume == Volume::zero() {
                let proof = self.sell_imt.match_order()?;
                self.finalize_match(proof, true)?;
            } else {
                let proof = self.sell_imt.match_partially(volume)?;
                self.finalize_partial_match(proof, true)?;
            }

            if match_leaf.volume == Volume::zero() {
                let proof = self.buy_imt.match_order()?;
                self.finalize_match(proof, false)?;
            } else {
                let proof = self.buy_imt.match_partially(volume)?;
                self.finalize_partial_match(proof, false)?;
            }
        }
        Ok(())
    }

    fn finalize_match<S: OrderSide>(
        &mut self,
        proof: MatchProof<S>,
        is_aggressive: bool,
    ) -> Result<(), IMTError> {
        let initial_state = self.state;
        let mut final_state = initial_state;
        let opcode = match S::SIDE {
            Side::Buy => {
                debug_assert_eq!(proof.initial_root, initial_state.buy_root);
                final_state.buy_root = self.buy_imt.root();
                final_state.best_buy_price = self.buy_imt.best_price_felts();
                if is_aggressive {
                    Opcode::MatchAggressiveBuy
                } else {
                    Opcode::MatchPassiveBuy
                }
            }
            Side::Sell => {
                debug_assert_eq!(proof.initial_root, initial_state.sell_root);
                final_state.sell_root = self.sell_imt.root();
                final_state.best_sell_price = self.sell_imt.best_price_felts();
                if is_aggressive {
                    Opcode::MatchAggressiveSell
                } else {
                    Opcode::MatchPassiveSell
                }
            }
        };
        final_state.n += BaseField::one();
        self.state = final_state;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
            opcode.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            proof.low_merkle_updated_path,
            IndexBits::<BaseField>::default(),
            proof.low_leaf.to_felts(),
            proof.match_leaf_proof,
            proof.match_leaf_path,
            proof.match_leaf_updated_path,
            proof.match_leaf_index,
            proof.match_leaf.to_felts(),
            final_state.n,
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
            BaseField::one()
        );
        self.trace.borrow_mut().add_instruction(instruction_felts);
        Ok(())
    }

    fn finalize_partial_match<S: OrderSide>(
        &mut self,
        proof: PartialMatchProof<S>,
        is_aggressive: bool,
    ) -> Result<(), IMTError> {
        let mut trace = self.trace.borrow_mut();
        let initial_state = self.state;
        let mut final_state = initial_state;
        let opcode = match S::SIDE {
            Side::Buy => {
                debug_assert_eq!(proof.initial_root, initial_state.buy_root);
                final_state.buy_root = self.buy_imt.root();
                final_state.best_buy_price = self.buy_imt.best_price_felts();
                if is_aggressive {
                    Opcode::PartialMatchAggressiveBuy
                } else {
                    Opcode::PartialMatchPassiveBuy
                }
            }
            Side::Sell => {
                debug_assert_eq!(proof.initial_root, initial_state.sell_root);
                final_state.sell_root = self.sell_imt.root();
                final_state.best_sell_price = self.sell_imt.best_price_felts();
                if is_aggressive {
                    Opcode::PartialMatchAggressiveSell
                } else {
                    Opcode::PartialMatchPassiveSell
                }
            }
        };
        final_state.n += BaseField::one();
        self.state = final_state;
        trace.add_add_event(
            proof.filled_volume.to_felts(),
            proof.remaining_volume.to_felts(),
        )?;
        let instruction_felts: [BaseField; N_INSTRUCTION_FELTS] = flatten!(
            initial_state.n,
            initial_state.buy_root,
            initial_state.best_buy_price,
            initial_state.sell_root,
            initial_state.best_sell_price,
            opcode.to_field(),
            proof.low_merkle_proof,
            proof.low_merkle_path,
            MerklePath::<BaseField>::default(),
            IndexBits::<BaseField>::default(),
            proof.filled_volume.to_felts(),
            proof.remaining_volume.to_felts(),
            [BaseField::zero(); N_LEAF_FELTS - 2 * N_U64_FELTS],
            proof.match_leaf_proof,
            proof.match_leaf_path,
            proof.match_leaf_updated_path,
            proof.match_leaf_index,
            proof.match_leaf.to_felts(),
            final_state.n,
            final_state.buy_root,
            final_state.best_buy_price,
            final_state.sell_root,
            final_state.best_sell_price,
            BaseField::one()
        );
        trace.add_instruction(instruction_felts);
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use tracing::{span, Level};

    use super::*;
    use crate::executor::instruction::InstructionColumn;
    use crate::imt::leaf::Leaf;
    use crate::{
        imt::{
            order::Order,
            side::{OrderSide, Side},
        },
        types::{Price, Time},
    };

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

    fn generate_random_order<S: OrderSide>(time: u64, base_price: u64) -> Order<BaseField, S> {
        let mut rng = rand::thread_rng();
        let price = match S::side() {
            Side::Buy => rng.gen_range(100..110),
            Side::Sell => rng.gen_range(100..=110),
        };
        let volume = rng.gen_range(1..=1000);
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
        let trace = std::mem::replace(&mut *trace.borrow_mut(), ExecutionTrace::new());
        debug!("Number of buy orders: {}", trace.buy_insert_order.len());
        debug!("Number of sell orders: {}", trace.sell_insert_order.len());
        debug!(
            "Number of aggressive buy matches: {}",
            trace.buy_aggressive_match.len()
        );
        debug!(
            "Number of passive buy matches: {}",
            trace.buy_passive_match.len()
        );
        debug!(
            "Number of aggressive sell matches: {}",
            trace.sell_aggressive_match.len()
        );
        debug!(
            "Number of passive sell matches: {}",
            trace.sell_passive_match.len()
        );
        debug!(
            "Number of Aggressive partial buy matches: {}",
            trace.buy_aggressive_partial_match.len()
        );
        debug!(
            "Number of Passive partial buy matches: {}",
            trace.buy_passive_partial_match.len()
        );
        debug!(
            "Number of Aggressive partial sell matches: {}",
            trace.sell_aggressive_partial_match.len()
        );
        debug!(
            "Number of Passive partial sell matches: {}",
            trace.sell_passive_partial_match.len()
        );
        debug!("Total number of instructions: {}", trace.instructions.len());
    }
    fn get_buy_leaf_safely(
        machine: &OrderBook,
        pt: PriceTime<BaseField, Buy>,
    ) -> Result<Leaf<BaseField, Buy>, String> {
        machine
            .buy_imt
            .get_leaf_by_price_time(pt.price().to_u64(), pt.time().to_u64())
            .map_err(|e| format!("Failed to get buy leaf for {:?}: {:?}", pt, e))
    }

    fn get_sell_leaf_safely(
        machine: &OrderBook,
        pt: PriceTime<BaseField, Sell>,
    ) -> Result<Leaf<BaseField, Sell>, String> {
        machine
            .sell_imt
            .get_leaf_by_price_time(pt.price().to_u64(), pt.time().to_u64())
            .map_err(|e| format!("Failed to get sell leaf for {:?}: {:?}", pt, e))
    }

    #[test]
    fn test_cancel_buy_order_simple() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time; // Get PriceTime

        // Place the order
        assert!(
            machine.place_buy_order(order.clone()).is_ok(),
            "Failed to place buy order"
        );

        // *** Check leaf exists AFTER insertion ***
        let leaf_after_insert =
            get_buy_leaf_safely(&machine, pt).expect("Leaf MUST exist immediately after insertion");
        assert!(
            leaf_after_insert.is_active(),
            "Leaf is inactive immediately after insertion"
        );

        let initial_state_before_cancel = machine.state.clone();
        let initial_root = machine.buy_imt.root();
        assert_eq!(trace.borrow().buy_insert_order.len(), 1);
        assert_eq!(trace.borrow().buy_delete_order.len(), 0);

        // Cancel the order
        let cancel_result = machine.cancel_buy_order(pt);
        // *** Check cancel result explicitly ***
        assert!(
            cancel_result.is_ok(),
            "cancel_buy_order failed: {:?}",
            cancel_result.err()
        );

        let final_state = machine.state.clone();

        // Check trace
        assert_eq!(trace.borrow().buy_insert_order.len(), 1);
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);

        // Check state transition counter 'n'
        assert_eq!(
            final_state.n,
            initial_state_before_cancel.n + BaseField::one()
        );

        // Check root hash changed
        assert_ne!(
            final_state.buy_root, initial_root,
            "Root hash did not change"
        );

        // Check if priority updated
        assert_eq!(
            final_state.best_buy_price,
            PriceTime::<BaseField, Buy>::last().price().to_felts(),
            "Priority not reset"
        );

        // Verify the correct opcode was added
        let binding = trace.borrow();
        let last_instruction = binding
            .instructions
            .last()
            .expect("Instruction trace empty");
        assert_eq!(
            last_instruction[InstructionColumn::OPCODE],
            Opcode::CancelBuyOrder.to_field()
        );
    }

    #[test]
    fn test_cancel_sell_order_simple() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order = Order::new(10, 100, 1);
        let pt = order.price_time; // Get PriceTime

        // Place the order
        assert!(
            machine.place_sell_order(order.clone()).is_ok(),
            "Failed to place sell order"
        );

        // *** Check leaf exists AFTER insertion ***
        let leaf_after_insert = get_sell_leaf_safely(&machine, pt)
            .expect("Leaf MUST exist immediately after insertion");
        assert!(
            leaf_after_insert.is_active(),
            "Leaf is inactive immediately after insertion"
        );

        let initial_state_before_cancel = machine.state.clone();
        let initial_root = machine.sell_imt.root();
        assert_eq!(trace.borrow().sell_insert_order.len(), 1);
        assert_eq!(trace.borrow().sell_delete_order.len(), 0);

        // Cancel the order
        let cancel_result = machine.cancel_sell_order(pt);
        // *** Check cancel result explicitly ***
        assert!(
            cancel_result.is_ok(),
            "cancel_sell_order failed: {:?}",
            cancel_result.err()
        );

        let final_state = machine.state.clone();

        // Check trace
        assert_eq!(trace.borrow().sell_insert_order.len(), 1);
        assert_eq!(trace.borrow().sell_delete_order.len(), 1);

        // Check state transition counter 'n'
        assert_eq!(
            final_state.n,
            initial_state_before_cancel.n + BaseField::one()
        );

        // Check root hash changed
        assert_ne!(
            final_state.sell_root, initial_root,
            "Root hash did not change"
        );

        // Check if priority updated
        assert_eq!(
            final_state.best_sell_price,
            PriceTime::<BaseField, Sell>::last().price().to_felts(),
            "Priority not reset"
        );

        // Verify the correct opcode was added
        let binding = trace.borrow();
        let last_instruction = binding
            .instructions
            .last()
            .expect("Instruction trace empty");
        assert_eq!(
            last_instruction[InstructionColumn::OPCODE],
            Opcode::CancelSellOrder.to_field()
        );
    }

    #[test]
    fn test_cancel_buy_order_updates_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Lower priority
        let order2 = Order::new(5, 110, 2); // Highest priority
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_buy_order(order1.clone()).is_ok());
        assert!(machine.place_buy_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert =
            get_buy_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert =
            get_buy_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order2
        assert_eq!(machine.state.best_buy_price, pt2.price().to_felts());

        // Cancel the highest priority order (order2)
        let cancel_result = machine.cancel_buy_order(pt2);
        assert!(
            cancel_result.is_ok(),
            "cancel_buy_order failed for pt2: {:?}",
            cancel_result.err()
        );

        // Verify priority updated to order1
        assert_eq!(machine.state.best_buy_price, pt1.price().to_felts());

        // Verify leaves state
        let leaf1 = get_buy_leaf_safely(&machine, pt1)
            .expect("Leaf 1 should still exist after cancelling leaf 2");
        assert!(leaf1.is_active());
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);
    }

    #[test]
    fn test_cancel_sell_order_updates_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Higher priority (lower price)
        let order2 = Order::new(5, 110, 2); // Lower priority
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_sell_order(order1.clone()).is_ok());
        assert!(machine.place_sell_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert =
            get_sell_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert =
            get_sell_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order1
        assert_eq!(machine.state.best_sell_price, pt1.price().to_felts());

        // Cancel the highest priority order (order1)
        let cancel_result = machine.cancel_sell_order(pt1);
        assert!(
            cancel_result.is_ok(),
            "cancel_sell_order failed for pt1: {:?}",
            cancel_result.err()
        );

        // Verify priority updated to order2
        assert_eq!(machine.state.best_sell_price, pt2.price().to_felts());

        // Verify leaves state
        let leaf2 = get_sell_leaf_safely(&machine, pt2)
            .expect("Leaf 2 should still exist after cancelling leaf 1");
        assert!(leaf2.is_active());
        assert_eq!(trace.borrow().sell_delete_order.len(), 1);
    }

    #[test]
    fn test_cancel_buy_order_does_not_update_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Lower priority - to be cancelled
        let order2 = Order::new(5, 110, 2); // Highest priority - remains
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_buy_order(order1.clone()).is_ok());
        assert!(machine.place_buy_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert =
            get_buy_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert =
            get_buy_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order2
        assert_eq!(machine.state.best_buy_price, pt2.price().to_felts());
        let initial_priority = machine.state.best_buy_price.clone();

        // Cancel the lower priority order (order1)
        let cancel_result = machine.cancel_buy_order(pt1);
        assert!(
            cancel_result.is_ok(),
            "cancel_buy_order failed for pt1: {:?}",
            cancel_result.err()
        );

        // Verify priority did NOT change
        assert_eq!(machine.state.best_buy_price, initial_priority);
        assert_eq!(machine.state.best_buy_price, pt2.price().to_felts()); // Still order2

        // Verify leaves state
        let leaf2 = get_buy_leaf_safely(&machine, pt2)
            .expect("Leaf 2 should still exist after cancelling leaf 1");
        assert!(leaf2.is_active());
        assert_eq!(trace.borrow().buy_delete_order.len(), 1);
    }

    #[test]
    fn test_cancel_sell_order_does_not_update_priority() {
        let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut machine = OrderBook::new(Rc::clone(&trace));
        let order1 = Order::new(10, 100, 1); // Highest priority - remains
        let order2 = Order::new(5, 110, 2); // Lower priority - to be cancelled
        let pt1 = order1.price_time;
        let pt2 = order2.price_time;

        // Place orders
        assert!(machine.place_sell_order(order1.clone()).is_ok());
        assert!(machine.place_sell_order(order2.clone()).is_ok());

        // *** Check leaves exist AFTER insertion ***
        let _leaf1_after_insert =
            get_sell_leaf_safely(&machine, pt1).expect("Leaf 1 MUST exist after insertion");
        let _leaf2_after_insert =
            get_sell_leaf_safely(&machine, pt2).expect("Leaf 2 MUST exist after insertion");

        // Verify initial priority is order1
        assert_eq!(machine.state.best_sell_price, pt1.price().to_felts());
        let initial_priority = machine.state.best_sell_price.clone();

        // Cancel the lower priority order (order2)
        let cancel_result = machine.cancel_sell_order(pt2);
        assert!(
            cancel_result.is_ok(),
            "cancel_sell_order failed for pt2: {:?}",
            cancel_result.err()
        );

        // Verify priority did NOT change
        assert_eq!(machine.state.best_sell_price, initial_priority);
        assert_eq!(machine.state.best_sell_price, pt1.price().to_felts()); // Still order1

        // Verify leaves state
        let leaf1 = get_sell_leaf_safely(&machine, pt1)
            .expect("Leaf 1 should still exist after cancelling leaf 2");
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
        let _leaf_after_insert =
            get_buy_leaf_safely(&machine, pt).expect("Leaf MUST exist after insertion");

        let initial_state = machine.state.clone();
        let trace_len_before = trace.borrow().instructions.len();

        // Attempt to cancel a non-existent order
        let result = machine.cancel_buy_order(non_existent_pt);
        assert!(
            result.is_err(),
            "Cancellation of non-existent order should fail"
        );
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
        let _leaf_after_insert =
            get_sell_leaf_safely(&machine, pt).expect("Leaf MUST exist after insertion");

        let initial_state = machine.state.clone();
        let trace_len_before = trace.borrow().instructions.len();

        // Attempt to cancel a non-existent order
        let result = machine.cancel_sell_order(non_existent_pt);
        assert!(
            result.is_err(),
            "Cancellation of non-existent order should fail"
        );
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
        assert!(
            cancel1_result.is_ok(),
            "First cancel failed: {:?}",
            cancel1_result.err()
        );

        let state_after_first_cancel = machine.state.clone();
        let trace_len_after_first_cancel = trace.borrow().instructions.len();

        // Attempt to cancel the already cancelled (inactive) order again
        let cancel2_result = machine.cancel_buy_order(pt);
        assert!(
            cancel2_result.is_err(),
            "Second cancellation of same order should fail"
        );
        // Check specific error if possible, e.g., CannotCancelInactive
        // assert!(matches!(cancel2_result.unwrap_err(), IMTError::CannotCancelInactive));

        // Verify state hasn't changed since the first cancel
        assert_eq!(machine.state, state_after_first_cancel);

        // Verify no *additional* cancel instruction was added
        assert_eq!(trace.borrow().buy_delete_order.len(), 1); // Still 1 cancel
        assert_eq!(
            trace.borrow().instructions.len(),
            trace_len_after_first_cancel
        );
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
        assert!(
            cancel1_result.is_ok(),
            "First cancel failed: {:?}",
            cancel1_result.err()
        );

        let state_after_first_cancel = machine.state.clone();
        let trace_len_after_first_cancel = trace.borrow().instructions.len();

        // Attempt to cancel the already cancelled (inactive) order again
        let cancel2_result = machine.cancel_sell_order(pt);
        assert!(
            cancel2_result.is_err(),
            "Second cancellation of same order should fail"
        );
        // assert!(matches!(cancel2_result.unwrap_err(), IMTError::CannotCancelInactive));

        // Verify state hasn't changed since the first cancel
        assert_eq!(machine.state, state_after_first_cancel);

        // Verify no *additional* cancel instruction was added
        assert_eq!(trace.borrow().sell_delete_order.len(), 1); // Still 1 cancel
        assert_eq!(
            trace.borrow().instructions.len(),
            trace_len_after_first_cancel
        );
    }
}

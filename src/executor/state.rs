use std::{array, fmt::Debug};

use stwo_prover::{constraint_framework::EvalAtRow, relation};

use crate::{
    executor::flatten_single,
    flatten,
    hash::N_HASH,
    imt::{Hash, PriceFelts, N_U64_FELTS},
};

pub type StateFelts<F> = [F; N_STATE_FELTS];

pub const N_STATE_FELTS: usize = 1 // n
    + N_HASH // buy_root
    + N_U64_FELTS // best_buy_price
    + N_HASH // sell_root
    + N_U64_FELTS // best_sell_price
    + 1; // op_code

/// State conists of root hashes and priority orders for Buy and Sell IMTs
#[derive(Clone, Copy, Debug, Default)]
pub struct State<F> {
    /// ith state
    pub n: F,
    /// root hash of the Buy IMT
    pub buy_root: Hash<F>,
    /// the order which should be matched first in the Buy IMT
    pub best_buy_price: PriceFelts<F>,
    /// root hash of the Sell IMT
    pub sell_root: Hash<F>,
    /// the order which should be matched first in the Sell IMT
    pub best_sell_price: PriceFelts<F>,
    /// the op code that resulted in this state
    pub op_code: F,
}

// StateElements are used and yielded in the processor component
// At each row, the processor uses the StateElements yielded by the previous row
// the number of elements used/yielded is equal to the number of columns in the State
relation!(StateElements, N_STATE_FELTS);

impl<F> State<F> {
    /// Creates a new State.
    pub fn new(
        n: F,
        buy_root: Hash<F>,
        best_buy_price: PriceFelts<F>,
        sell_root: Hash<F>,
        best_sell_price: PriceFelts<F>,
        op_code: F,
    ) -> Self {
        State {
            n,
            buy_root,
            best_buy_price,
            sell_root,
            best_sell_price,
            op_code,
        }
    }

    /// from_eval returns a State instance from a given EvalAtRow instance
    pub fn from_eval<E: EvalAtRow>(eval: &mut E) -> State<E::F> {
        let n = eval.next_trace_mask();
        let buy_root = array::from_fn(|_| eval.next_trace_mask());
        let best_buy_price = array::from_fn(|_| eval.next_trace_mask());
        let sell_root = array::from_fn(|_| eval.next_trace_mask());
        let best_sell_price = array::from_fn(|_| eval.next_trace_mask());
        let op_code = eval.next_trace_mask();
        State {
            n,
            buy_root,
            best_buy_price,
            sell_root,
            best_sell_price,
            op_code,
        }
    }
}

impl<F: Clone + Debug + Copy> State<F> {
    pub fn to_felts(&self) -> [F; N_STATE_FELTS] {
        flatten!(
            self.n,
            self.buy_root,
            self.best_buy_price,
            self.sell_root,
            self.best_sell_price,
            self.op_code
        )
    }
}

pub struct StateColumn;

impl StateColumn {
    pub const N: usize = 0;
    pub const BUY_ROOT: usize = Self::N + 1;
    pub const BEST_BUY_PRICE: usize = Self::BUY_ROOT + N_HASH;
    pub const SELL_ROOT: usize = Self::BEST_BUY_PRICE + N_U64_FELTS;
    pub const BEST_SELL_PRICE: usize = Self::SELL_ROOT + N_HASH;
    pub const N_STATE_FELTS: usize = Self::BEST_SELL_PRICE + N_U64_FELTS;
}

use std::array;

use stwo_prover::{constraint_framework::EvalAtRow, relation};

use crate::{
    hash::N_HASH,
    imt::{Hash, PriceTimeFelts, N_U64_FELTS},
};

pub const N_STATE_FELTS: usize = 1 // n
    + N_HASH // buy_root_hash
    + 2 * N_U64_FELTS // buy_imt_priority
    + N_HASH // sell_root_hash
    + 2 * N_U64_FELTS; // sell_imt_priority

/// State conists of root hashes and priority orders for Buy and Sell IMTs
#[derive(Clone, Copy, Debug)]
pub struct State<F> {
    /// ith state
    pub n: F,
    /// root hash of the Buy IMT
    pub buy_root_hash: Hash<F>,
    /// the order which should be matched first in the Buy IMT
    pub buy_imt_priority: PriceTimeFelts<F>,
    /// root hash of the Sell IMT
    pub sell_root_hash: Hash<F>,
    /// the order which should be matched first in the Sell IMT
    pub sell_imt_priority: PriceTimeFelts<F>,
}

// StateElements are used and yielded in the processor component
// At each row, the processor uses the StateElements yielded by the previous row
// the number of elements used/yielded is equal to the number of columns in the State
relation!(StateElements, N_STATE_FELTS);

impl<F> State<F> {
    /// Creates a new State.
    pub fn new(
        n: F,
        buy_root_hash: Hash<F>,
        buy_imt_priority: PriceTimeFelts<F>,
        sell_root_hash: Hash<F>,
        sell_imt_priority: PriceTimeFelts<F>,
    ) -> Self {
        State {
            n,
            buy_root_hash,
            buy_imt_priority,
            sell_root_hash,
            sell_imt_priority,
        }
    }

    /// from_eval returns a State instance from a given EvalAtRow instance
    pub fn from_eval<E: EvalAtRow>(eval: &mut E) -> State<E::F> {
        let n = eval.next_trace_mask();
        let buy_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let buy_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        let sell_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let sell_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        State {
            n,
            buy_root_hash,
            buy_imt_priority,
            sell_root_hash,
            sell_imt_priority,
        }
    }
}

use std::array;

use stwo_prover::{
    constraint_framework::EvalAtRow,
    core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE},
};

use crate::{
    executor::instruction::{Instruction, N_INSTRUCTION_FELTS},
    hash::N_HASH,
    imt::N_LEAF_FELTS,
};

use super::TraceSize;

// mod constraints;
mod trace;

// pub use trace::{interaction_trace, preprocessed_trace, trace};

// pub use trace::{interaction_trace, preprocessed_trace, trace};

/// Insertion Instructions
pub type ProcessorRows = Vec<[BaseField; ProcessorColumn::MAIN_COLS]>;

pub struct ProcessorRow<F> {
    pub initial_state: F,
    pub initial_buy_root_hash: [F; N_HASH],
    pub initial_buy_imt_priority: [F; N_LEAF_FELTS],
    pub initial_sell_root_hash: [F; N_HASH],
    pub initial_sell_imt_priority: [F; N_LEAF_FELTS],
    pub instruction: Instruction<F>,
    pub final_state: F,
    pub final_buy_root_hash: [F; N_HASH],
    pub final_buy_imt_priority: [F; N_LEAF_FELTS],
    pub final_sell_root_hash: [F; N_HASH],
    pub final_sell_imt_priority: [F; N_LEAF_FELTS],
    pub is_real: F,
}

impl<F> ProcessorRow<F> {
    pub fn from_eval<E: EvalAtRow>(eval: &mut E) -> ProcessorRow<E::F> {
        let initial_state = eval.next_trace_mask();
        let initial_buy_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let initial_buy_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        let initial_sell_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let initial_sell_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        let instruction = Instruction::<E::F>::from_eval::<E>(eval);
        let final_state = eval.next_trace_mask();
        let final_buy_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let final_buy_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        let final_sell_root_hash = array::from_fn(|_| eval.next_trace_mask());
        let final_sell_imt_priority = array::from_fn(|_| eval.next_trace_mask());
        let is_real = eval.next_trace_mask();
        ProcessorRow {
            initial_state,
            initial_buy_root_hash,
            initial_buy_imt_priority,
            initial_sell_root_hash,
            initial_sell_imt_priority,
            instruction,
            final_state,
            final_buy_root_hash,
            final_buy_imt_priority,
            final_sell_root_hash,
            final_sell_imt_priority,
            is_real,
        }
    }
}

/// Insertions Column
/// Each row of the trace is a InsertionsOp field elements arranged as per the `InsertionsColumn`
/// The last field is a flag to indicate if the row is real or padded
#[derive(Debug, Clone)]
pub struct ProcessorColumn;

impl ProcessorColumn {
    /// Initial State Number for Si is i
    pub const INITIAL_STATE: usize = 0;
    /// Initial Buy Root Hash
    pub const INITIAL_BUY_ROOT_HASH: usize = Self::INITIAL_STATE + 1;
    /// Initial Buy IMT Priority
    pub const INITIAL_BUY_IMT_PRIORITY: usize = Self::INITIAL_BUY_ROOT_HASH + N_HASH;
    /// Initial Sell Root Hash
    pub const INITIAL_SELL_ROOT_HASH: usize = Self::INITIAL_BUY_IMT_PRIORITY + N_LEAF_FELTS;
    /// Initial Sell IMT Priority
    pub const INITIAL_SELL_IMT_PRIORITY: usize = Self::INITIAL_SELL_ROOT_HASH + N_HASH;
    /// Instruction
    pub const INSTRUCTION: usize = Self::INITIAL_SELL_IMT_PRIORITY + N_LEAF_FELTS;
    /// Final State Number for Si is i + 1
    pub const FINAL_STATE: usize = Self::INSTRUCTION + N_INSTRUCTION_FELTS;
    /// Final Buy Root Hash
    pub const FINAL_BUY_ROOT_HASH: usize = Self::FINAL_STATE + 1;
    /// Final Buy IMT Priority
    pub const FINAL_BUY_IMT_PRIORITY: usize = Self::FINAL_BUY_ROOT_HASH + N_HASH;
    /// Final Sell Root Hash
    pub const FINAL_SELL_ROOT_HASH: usize = Self::FINAL_BUY_IMT_PRIORITY + N_LEAF_FELTS;
    /// Final Sell IMT Priority
    pub const FINAL_SELL_IMT_PRIORITY: usize = Self::FINAL_SELL_ROOT_HASH + N_HASH;
    /// Total Columns
    pub const N_COLS: usize = Self::FINAL_SELL_IMT_PRIORITY + N_LEAF_FELTS;
}

impl TraceSize for ProcessorColumn {
    const MAIN_COLS: usize = Self::N_COLS;
    const INTERACTION_COLS: usize = 2 * SECURE_EXTENSION_DEGREE;
}

// #[cfg(test)]
// mod tests {
//     use std::{cell::RefCell, marker::PhantomData, rc::Rc};

//     use constraints::InsertionsEval;
//     use rand::Rng;
//     use stwo_prover::{
//         constraint_framework::{assert_constraints, FrameworkEval},
//         core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
//     };
//     use trace::{interaction_trace, preprocessed_trace, trace};
//     use tracing::{span, Level};

//     use crate::{
//         components::{
//             less_than::{LessThanElements, StrictLessThanElements},
//             poseidon::PoseidonElements,
//         },
//         executor::{instruction::InstructionElements, record::ExecutionTrace},
//         imt::{
//             order::Order,
//             side::{Buy, OrderSide, Sell},
//             BuyIMT, SellIMT,
//         },
//     };

//     use super::*;

//     fn evaluate_trace<S: OrderSide>(
//         insertions: Insertions,
//         poseidon_elements: &PoseidonElements,
//         less_than_elements: &LessThanElements,
//         strict_less_than_elements: &StrictLessThanElements,
//         instruction_elements: &InstructionElements,
//     ) {
//         let log_size = (insertions.len() - 1).ilog2() + 1;
//         let constant_trace = preprocessed_trace(log_size);
//         let (trace, claim) = trace::<S>(insertions);
//         let (interaction_trace, interaction_claim) = interaction_trace::<S>(
//             &trace,
//             poseidon_elements,
//             less_than_elements,
//             strict_less_than_elements,
//             instruction_elements,
//         );

//         let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
//         let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

//         let component: InsertionsEval<S> = InsertionsEval {
//             less_than_elements: less_than_elements.clone(),
//             poseidon_elements: poseidon_elements.clone(),
//             strict_less_than_elements: strict_less_than_elements.clone(),
//             instruction_elements: instruction_elements.clone(),
//             _side: PhantomData,
//             claim,
//         };

//         assert_constraints(
//             &trace_polys,
//             CanonicCoset::new(log_size),
//             |eval| {
//                 component.evaluate(eval);
//             },
//             interaction_claim.claimed_sum,
//         );
//     }

//     #[test_log::test]
//     fn test_insertions_table() {
//         // Execution Record
//         let span = span!(Level::INFO, "Generating Execution Record").entered();
//         let record = Rc::new(RefCell::new(ExecutionTrace::new()));
//         let mut buy_imt = BuyIMT::new(Rc::clone(&record));
//         let mut sell_imt = SellIMT::new(Rc::clone(&record));
//         let mut rng = rand::thread_rng();
//         let mut time = 1;
//         let n = 48;
//         for _ in 0..n {
//             let time_inc = rng.gen_range(1..=16);
//             time += time_inc;
//             let buy_order = Order::new(rng.gen(), rng.gen(), time);
//             let sell_order = Order::new(rng.gen(), rng.gen(), time);
//             buy_imt.insert(buy_order).unwrap();
//             sell_imt.insert(sell_order).unwrap();
//         }

//         let execution_trace = std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
//         span.exit();

//         // Fiat Shamir Channel
//         let mut channel = Blake2sChannel::default();

//         // Relation Elements
//         let poseidon_elements = PoseidonElements::draw(&mut channel);
//         let less_than_elements = LessThanElements::draw(&mut channel);
//         let strict_less_than_elements = StrictLessThanElements::draw(&mut channel);
//         let instruction_elements = InstructionElements::draw(&mut channel);

//         // Evaluations Buy IMT
//         evaluate_trace::<Buy>(
//             execution_trace.buy_insert_order,
//             &poseidon_elements,
//             &less_than_elements,
//             &strict_less_than_elements,
//             &instruction_elements,
//         );

//         // Evaluations Sell IMT
//         evaluate_trace::<Sell>(
//             execution_trace.sell_insert_order,
//             &poseidon_elements,
//             &less_than_elements,
//             &strict_less_than_elements,
//             &instruction_elements,
//         );
//     }
// }

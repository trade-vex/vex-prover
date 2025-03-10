use crate::types::N_U64_LIMBS;
use std::array;
use stwo_prover::{
    constraint_framework::{EvalAtRow, FrameworkComponent},
    core::fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE},
    relation,
};

use super::TraceSize;
mod constraints;
mod trace;

pub use constraints::LessThanEval;
pub use trace::{interaction_trace_eval, preprocessed_trace, trace_eval};

/// LessThanComponent represents the LessThan component
pub type StrictLessThanComponent = FrameworkComponent<LessThanEval<true>>;
pub type LessThanComponent = FrameworkComponent<LessThanEval<false>>;

/// Less Than Operations
pub type LessThanOperations = Vec<[BaseField; LessThanColumn::MAIN_COLS]>;

/// LessThanOp represents the LessThan operation between two uint represented as N u8 limbs.
/// Example for BaseField = M31 and uint64_t: N = 8
#[derive(Debug)]
pub struct LessThanOp<F> {
    // first operand
    a: [F; N_U64_LIMBS],
    // second operand
    b: [F; N_U64_LIMBS],
    // result of the comparison
    c: F,
    // flag is 1 for the most significant byte where a[i] is not equal to b[i]
    // flag is 1 for the most significant byte where a[i] is not equal to b[i]
    flags: [F; N_U64_LIMBS],
    // First byte of the first operand where a[i] is not equal to b[i] from the most significant byte
    a_comparison_byte: F,
    // First byte of the second operand where a[i] < b[i] from the most significant byte
    b_comparison_byte: F,
    // is real flag to check if the operation is not among the dummy padded operations
    is_real: F,
}

impl<F> LessThanOp<F> {
    /// from_eval returns a LessThanOp instance from a given EvalAtRow instance
    fn from_eval<E: EvalAtRow>(eval: &mut E) -> LessThanOp<E::F> {
        let a = array::from_fn(|_| eval.next_trace_mask());
        let b = array::from_fn(|_| eval.next_trace_mask());
        let c = eval.next_trace_mask();
        let flags = array::from_fn(|_| eval.next_trace_mask());
        let a_comparison_byte = eval.next_trace_mask();
        let b_comparison_byte = eval.next_trace_mask();
        let is_real = eval.next_trace_mask();
        LessThanOp {
            a,
            b,
            c,
            flags,
            a_comparison_byte,
            b_comparison_byte,
            is_real,
        }
    }
}

/// LessThanColumn represents a Column for the starting limb of a field in LessThanOp
#[derive(Debug, Clone)]
pub struct LessThanColumn;

impl LessThanColumn {
    pub const A: usize = 0;
    pub const B: usize = Self::A + N_U64_LIMBS;
    pub const C: usize = Self::B + N_U64_LIMBS;
    pub const FLAGS: usize = Self::C + 1;
    pub const A_COMPARISON_BYTE: usize = Self::FLAGS + N_U64_LIMBS;
    pub const B_COMPARISON_BYTE: usize = Self::A_COMPARISON_BYTE + 1;
    pub const IS_REAL: usize = Self::B_COMPARISON_BYTE + 1;
}

impl TraceSize for LessThanColumn {
    // is_first column
    const PREPROCESSED_COLS: usize = 1;
    // last field's index + offset
    const MAIN_COLS: usize = Self::IS_REAL + 1;
    // 1 Interaction Column for LessThanU8 check
    // 1 Interaction Column for yielding the result
    const INTERACTION_COLS: usize = SECURE_EXTENSION_DEGREE;
}

// A Total of 17 elements are "used" or "yielded" for the less than operation
// a - 8 limbs corresponding to the first operand(u64)
// b - 8 limbs corresponding to the second operand(u64)
// c - 1 limb corresponding to the result of the comparison
relation!(LessThanElements, 17);
relation!(StrictLessThanElements, 17);

#[cfg(test)]
mod tests {
    use constraints::LessThanEval;
    use rand::Rng;
    use std::{cell::RefCell, rc::Rc};
    use stwo_prover::{
        constraint_framework::{assert_constraints, FrameworkEval},
        core::{channel::Blake2sChannel, pcs::TreeVec, poly::circle::CanonicCoset},
    };
    use trace::{interaction_trace_eval, preprocessed_trace, trace_eval};
    use tracing::{span, Level};

    use crate::{
        components::bytes::LessThanU8Elements,
        executor::record::ExecutionTrace,
        imt::{order::Order, BuyIMT, SellIMT},
        types::Price,
    };

    use super::*;

    fn evaluate_trace<const STRICT: bool>(
        less_than_operations: LessThanOperations,
        less_than_u8_elements: &LessThanU8Elements,
        less_than_elements: &LessThanElements,
        strict_less_than_elements: &StrictLessThanElements,
    ) {
        let log_size = (less_than_operations.len() - 1).ilog2() + 1;
        let constant_trace = preprocessed_trace(log_size);
        let (trace, claim) = trace_eval::<STRICT>(less_than_operations);
        let (interaction_trace, interaction_claim) = if STRICT {
            interaction_trace_eval::<STRICT, _>(
                &trace,
                less_than_u8_elements,
                strict_less_than_elements,
            )
        } else {
            interaction_trace_eval::<STRICT, _>(&trace, less_than_u8_elements, less_than_elements)
        };

        let trace = TreeVec::new(vec![constant_trace, trace, interaction_trace]);
        let trace_polys = TreeVec::<Vec<_>>::map_cols(trace, |c| c.interpolate());

        let component: LessThanEval<STRICT> = LessThanEval {
            less_than_u8_elements: less_than_u8_elements.clone(),
            less_than_elements: less_than_elements.clone(),
            strict_less_than_elements: strict_less_than_elements.clone(),
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
    fn test_less_than_table() {
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
        let less_than_u8_elements = LessThanU8Elements::draw(&mut channel);
        let less_than_elements = LessThanElements::draw(&mut channel);
        let strict_less_than_elements = StrictLessThanElements::draw(&mut channel);

        evaluate_trace::<false>(
            execution_trace.less_than_operations,
            &less_than_u8_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );
        evaluate_trace::<true>(
            execution_trace.strict_less_than_operations,
            &less_than_u8_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );
    }

    #[test_log::test]
    fn test_less_than_constraints() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let mut execution_trace = ExecutionTrace::new();
        let mut rng = rand::thread_rng();

        // add a=b operations
        for _ in 0..16 {
            let a: [BaseField; N_U64_LIMBS] = Price::from_u64(rng.gen()).to_felts();
            execution_trace.add_less_than_event(a, a).unwrap();
            execution_trace.add_strictly_less_than_event(a, a).unwrap();
        }
        for _ in 0..1 << 16 {
            let a: [BaseField; N_U64_LIMBS] = Price::from_u64(rng.gen()).to_felts();
            let b: [BaseField; N_U64_LIMBS] = Price::from_u64(rng.gen()).to_felts();
            execution_trace.add_less_than_event(a, b).unwrap();
            execution_trace.add_strictly_less_than_event(a, b).unwrap();
        }

        span.exit();

        // Fiat Shamir Channel
        let mut channel = Blake2sChannel::default();

        // Relation Elements
        let less_than_u8_elements = LessThanU8Elements::draw(&mut channel);
        let less_than_elements = LessThanElements::draw(&mut channel);
        let strict_less_than_elements = StrictLessThanElements::draw(&mut channel);
        evaluate_trace::<false>(
            execution_trace.less_than_operations,
            &less_than_u8_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );
        evaluate_trace::<true>(
            execution_trace.strict_less_than_operations,
            &less_than_u8_elements,
            &less_than_elements,
            &strict_less_than_elements,
        );
    }
}

use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use std::array;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_prover::{
    constraint_framework::{
        logup::LogupTraceGenerator, EvalAtRow, FrameworkComponent, FrameworkEval, Relation,
        RelationEntry,
    },
    core::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::{PackedQM31, PackedSecureField},
            SimdBackend,
        },
        fields::{m31::BaseField, secure_column::SECURE_EXTENSION_DEGREE},
        poly::{
            circle::{CanonicCoset, CircleEvaluation},
            BitReversedOrder,
        },
        ColumnVec,
    },
    relation,
};
use tracing::{span, Level};

use super::{Claim, InteractionClaim, TraceSize};
use crate::{
    components::is_real_col,
    constants::{EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS},
    hash::{
        apply_external_round_matrix, apply_internal_round_matrix, pow5, N_ELEMENTS, N_FULL_ROUNDS,
        N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS, N_STATE,
    },
};

pub const N_LOG_INSTANCES_PER_ROW: usize = 3;
pub const N_INSTANCES_PER_ROW: usize = 1 << N_LOG_INSTANCES_PER_ROW;
/// Index: 0-16: Initial State
/// Index: 16-80: First 4 Full Rounds End: 16 + 4 * 16 = 80
/// Index: 80-94: 14 Partial Rounds End Applied to state[0]: 80 + 14 = 94
/// Index: 94-158: Last 4 Full Rounds End: 94 + 4 * 16 = 158
const N_COLUMNS_PER_REP: usize = N_STATE + N_STATE * N_FULL_ROUNDS + N_PARTIAL_ROUNDS;
// N_INSTANCES_PER_ROW * N_COLUMNS_PER_REP + 1 (is_real)
const N_COLUMNS: usize = N_INSTANCES_PER_ROW * N_COLUMNS_PER_REP + 1;
pub const LOG_EXPAND: u32 = 2;

/// Poseidon Operations
/// Contains Initial State before the permutation.
pub type PoseidonOperations = Vec<[BaseField; N_STATE]>;

/// PoseidonComponent is a component that evaluates the Poseidon2 Permutation.
pub type PoseidonComponent = FrameworkComponent<PoseidonEval>;

// The Elements "Used" & "Yielded" consists of the initial state
// and the final hash.
// The Initial state consists of 16 M31 elements and the final hash
// consists of 8 M31 elements.
relation!(PoseidonElements, N_ELEMENTS);

#[derive(Clone)]
pub struct PoseidonEval {
    pub claim: Claim<PoseidonColumn>,
    pub poseidon_elements: PoseidonElements,
}

impl FrameworkEval for PoseidonEval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + LOG_EXPAND
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // is_real determines if the operation is from a non-padded row.
        let is_real = eval.next_trace_mask();

        // is_real must be a boolean.
        eval.add_constraint(is_real.clone() * (is_real.clone() - E::F::one()));

        for _ in 0..N_INSTANCES_PER_ROW {
            let mut state: [_; N_STATE] = std::array::from_fn(|_| eval.next_trace_mask());

            // Initial state is added to the relation.
            let initial_state = state.clone();

            // First Half full rounds.
            (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                (0..N_STATE).for_each(|i| {
                    state[i] += EXTERNAL_ROUND_CONSTS[round][i];
                });
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i].clone()));
                state.iter_mut().for_each(|s| {
                    let m = eval.next_trace_mask();
                    eval.add_constraint(s.clone() - m.clone());
                    *s = m;
                });
            });

            // Partial rounds.
            (0..N_PARTIAL_ROUNDS).for_each(|round| {
                state[0] += INTERNAL_ROUND_CONSTS[round];
                apply_internal_round_matrix(&mut state);
                state[0] = pow5(state[0].clone());
                let m = eval.next_trace_mask();
                eval.add_constraint(state[0].clone() - m.clone());
                state[0] = m;
            });

            // Last Half full rounds.
            (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                (0..N_STATE).for_each(|i| {
                    state[i] += EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i];
                });
                apply_external_round_matrix(&mut state);
                state = std::array::from_fn(|i| pow5(state[i].clone()));
                state.iter_mut().for_each(|s| {
                    let m = eval.next_trace_mask();
                    eval.add_constraint(s.clone() - m.clone());
                    *s = m;
                });
            });

            // Add Initial State and hash to the relation.
            let values = initial_state.iter().chain(&state[0..8]);
            eval.add_to_relation(RelationEntry::new(
                &self.poseidon_elements,
                -E::EF::from(is_real.clone()),
                &values.map(|s| s.clone()).collect_vec(),
            ))
        }

        eval.finalize_logup();
        eval
    }
}

/// Poseidon Trace
pub fn trace(
    mut poseidon_operations: PoseidonOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<PoseidonColumn>,
) {
    let _span = span!(Level::INFO, "Poseidon: Main Trace").entered();
    let log_size = (poseidon_operations.len() / N_INSTANCES_PER_ROW - 1).ilog2() + 1;

    // is_real column is used to determine if the operation is from a non-padded row.
    let is_real = is_real_col(poseidon_operations.len() / N_INSTANCES_PER_ROW);

    // pad the operations to the next power of 2.
    for _ in 0..(1 << log_size) * N_INSTANCES_PER_ROW - poseidon_operations.len() {
        poseidon_operations.push([BaseField::zero(); N_STATE]);
    }

    // the number of columns is 1 less than the number of operations.
    // as the is_real column is not included in the operations
    // it is added separately.
    let mut trace = ComponentTrace::<{ PoseidonColumn::MAIN_COLS - 1 }>::zeroed(log_size);

    trace
        .par_iter_mut()
        .zip(
            poseidon_operations
                .par_iter()
                .chunks(N_LANES * N_INSTANCES_PER_ROW)
                .into_par_iter(),
        )
        .for_each(|(mut row, data)| {
            let mut col_index = 0;
            for rep_i in 0..N_INSTANCES_PER_ROW {
                // Initial state.
                let mut state: [PackedBaseField; N_STATE] = array::from_fn(|j| {
                    PackedBaseField::from_array(array::from_fn(|i| data[N_LANES * rep_i + i][j]))
                });

                state.iter().copied().for_each(|s| {
                    *row[col_index] = s;
                    col_index += 1;
                });

                // 4 full rounds.
                (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                    (0..N_STATE).for_each(|i| {
                        state[i] += PackedBaseField::broadcast(EXTERNAL_ROUND_CONSTS[round][i]);
                    });
                    apply_external_round_matrix(&mut state);
                    state = std::array::from_fn(|i| pow5(state[i]));
                    state.iter().copied().for_each(|s| {
                        *row[col_index] = s;
                        col_index += 1;
                    });
                });

                // Partial rounds.
                (0..N_PARTIAL_ROUNDS).for_each(|round| {
                    state[0] += PackedBaseField::broadcast(INTERNAL_ROUND_CONSTS[round]);
                    apply_internal_round_matrix(&mut state);
                    state[0] = pow5(state[0]);
                    *row[col_index] = state[0];
                    col_index += 1;
                });

                // 4 full rounds.
                (0..N_HALF_FULL_ROUNDS).for_each(|round| {
                    (0..N_STATE).for_each(|i| {
                        state[i] += PackedBaseField::broadcast(
                            EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i],
                        );
                    });
                    apply_external_round_matrix(&mut state);
                    state = std::array::from_fn(|i| pow5(state[i]));
                    state.iter().copied().for_each(|s| {
                        *row[col_index] = s;
                        col_index += 1;
                    });
                });
            }
        });

    let is_real_eval = CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(
        CanonicCoset::new(log_size).circle_domain(),
        is_real,
    );

    let trace = chain!([is_real_eval], trace.to_evals()).collect_vec();
    (trace, Claim::new(log_size))
}

/// Poseidon Interaction Trace
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    poseidon_elements: &PoseidonElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<PoseidonColumn>,
) {
    let _span = span!(Level::INFO, "Poseidon: Interaction Trace").entered();

    let log_size = trace[0].domain.log_size();
    let is_real_col = &trace[0].data;
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    for rep_i in 0..N_INSTANCES_PER_ROW {
        let mut col_gen = logup_gen.new_col();
        for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
            // fetch the initial state and the final hash from the trace.
            let values: [PackedBaseField; N_ELEMENTS] = array::from_fn(|i| {
                if i < 16 {
                    trace[N_COLUMNS_PER_REP * rep_i + 1 + i].data[vec_row]
                } else {
                    trace[N_COLUMNS_PER_REP * rep_i + 143 + i - 16].data[vec_row]
                }
            });
            let denom0: PackedSecureField = poseidon_elements.combine(&values);
            // the multiplicity is negative as the output is "yielded".
            col_gen.write_frac(vec_row, -PackedQM31::one() * is_real_col[vec_row], denom0);
        }
        col_gen.finalize_col();
    }
    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}

#[derive(Debug, Clone)]
pub struct PoseidonColumn;

impl TraceSize for PoseidonColumn {
    const MAIN_COLS: usize = N_COLUMNS;
    const INTERACTION_COLS: usize = N_INSTANCES_PER_ROW * N_ELEMENTS * SECURE_EXTENSION_DEGREE;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{executor::record::ExecutionTrace, imt::order::Order, imt::BuyIMT};
    use rand::Rng;
    use stwo_prover::{
        constraint_framework::{assert_constraints, preprocessed_columns::IsFirst},
        core::{pcs::TreeVec, poly::circle::CanonicCoset},
    };

    #[test_log::test]
    fn test_poseidon_constraints() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let mut record = ExecutionTrace::new();
        let mut imt = BuyIMT::new(&mut record);
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 48;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            let order = Order::new(rng.gen(), rng.gen(), time);
            imt.insert(order).unwrap();
        }
        let log_size = (record.poseidon_operations.len() / N_INSTANCES_PER_ROW - 1).ilog2() + 1;
        span.exit();

        // Trace.
        let (trace, claim) = trace(record.poseidon_operations);
        let poseidon_elements = PoseidonElements::dummy();
        let (interaction_trace, interaction_claim) = interaction_trace(&trace, &poseidon_elements);

        let traces = TreeVec::new(vec![
            vec![IsFirst::new(log_size).gen_column_simd()],
            trace,
            interaction_trace,
        ]);
        let trace_polys =
            traces.map(|trace| trace.into_iter().map(|c| c.interpolate()).collect_vec());

        // Constraint Evaluation.
        let component = PoseidonEval {
            poseidon_elements,
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
}

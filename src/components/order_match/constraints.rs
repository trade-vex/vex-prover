use crate::{
    components::constraints_utils::eval_merkle_proof,
    executor::{flatten_single, instruction::IMTOperation},
    imt::{
        leaf::Leaf,
        side::{MatchType, OrderMatchType},
        N_LEAF_FELTS,
    },
};
use std::{array, marker::PhantomData};

use itertools::{chain, Itertools};
use num_traits::{One, Zero};
use stwo_prover::constraint_framework::{EvalAtRow, FrameworkEval, RelationEntry};

use crate::{
    components::{less_than::LessThanElements, poseidon::PoseidonElements, Claim},
    executor::instruction::{Instruction, InstructionElements},
    flatten,
    hash::N_HASH,
    imt::{
        leaf::LeafColumn,
        side::{OrderSide, Side},
        MERKLE_HEIGHT, N_U64_FELTS,
    },
};

use super::{MatchColumn, MatchElements};

#[derive(Clone)]
pub struct MatchEval<S, T: OrderMatchType> {
    pub claim: Claim<MatchColumn<T>>,
    pub poseidon_elements: PoseidonElements,
    pub less_than_elements: LessThanElements,
    pub instruction_elements: InstructionElements,
    pub match_elements: MatchElements,
    pub _side: PhantomData<S>,
    pub _type: PhantomData<T>,
}

/// This implementation of the `FrameworkEval` trait for `MatchEval` provides methods to evaluate
/// constraints on Order Matches to Buy and Sell IMT;
///
/// The Implementation is Generic over the Order Side and Order Match Type.
///
/// # Constaint Evaluation
///
/// - `evaluate<E: EvalAtRow>(&self, mut eval: E) -> E`:
///
/// The Constraint Evaluation is done for
///  1. The Initial State must be in sync with the merkle proofs.
///  1. The Merkle Proofs must be verified correctly.
///  2. The Final State must be updated correctly.
///
///  Order Match Operation within a Single IMT:
///  1) Updating the 0th Leaf's next value to point to the next leaf of the matched leaf.
///  2) Switch the active flag of the matched leaf to 0.
///  The constraints must ensure that the low leaf in the instruction is the first leaf in the tree.
///  The constraints must ensure that the updates are done correctly.
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. The Matched Leaf must be active.
///   3. Assert that the opcode is equal to the operation's opcode. // different for side + type combination
///   4. Todo constraint:- The Op code that precedes the current operation must be correct.
///        - Aggressive Match: The previous operation must be an insert operation on the same side.
///        - Passive Match: The previous operation must be an aggressive match operation on the opposite side.
///          Note - The previous operation can be either full or partial match.
///   5. Check For the Match Invairant:(This Check is only for Aggressive Match)
///      - Invariant: MAX(buy_imt) >= MIN(sell_imt)
///      - On Buy Side: leaf.price >= initial_state.best_sell_price(trade_price), less_than_values [trade_price, leaf.price, 1]
///      - On Sell Side: leaf.price <= initial_state.best_buy_price(trade_price), less_than_values [leaf.price, trade_price, 1]
///      - The Match Elements are yielded, Match Elements consist of (price, volume) pair.
///      - Todo: This must contain the side of the aggressive side, like 0/1
///      - Todo: This must contain Trade_ID
///   6. Use The Match Elements:(This Check is only for Passive Match)
///      - Since the trade_price is always set by the passive side, the leaf price, volume is directly used.
///   4. The Low Leaf must be the first leaf in the tree and should point to the matched leaf.
///      - The Low Leaf's active flag must be set to 1.
///      - The Low Leaf's volume must be equal to zero.
///      - The Low Leaf's price_time must be equal to the first price_time in the tree.
///      - The Low Leaf's next value must be equal to the Matched Leaf.
///     Note: Instead of adding constraints, the low leaf can be constructed with the eval function.
///           Because there is not arithmetic involved in the construction, the constraints can be avoided.
///   6. Assert that the initial root hash of the initial state is equal to the root hash in the merkle path of the low/0th leaf.
///   8. The Low leaf is part of the Merkle Tree by verifying the Merkle Proof.
///      - The Merkle Proof is a list of sibling hashes from the leaf to the root.
///      - The Merkle Path is a list of hashes from the leaf to the root.
///      - IndexBits is the binary representation of the index of the leaf.
///   9. Update the Low Leaf's next value by replacing the "next" value with the "next" of the matched leaf.
///   10. Ensure that the resultant root hash from updating the low leaf is equal to the root contained in matched leaf's merkle path
///       as both operations are contiguous.
///   11. Verify the Merkle Proof of the Matched Leaf.
///   12. Update the Matched Leaf's active flag to 0.
///   13. Ensure that the final state's count is equal to the initial state's count + 1.
///   14. Ensure that the resulting root hash from update of matched leaf's is equal to the final state's root hash.
///   15. Ensure That the final state values for the other side of the tree are same as the initial state values.
///   16. Ensure that the final state's priority is equal to the matched leaf's next price_time.
///   16. Yield the Results by adding the values to the ProcessorLookupElements.   
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///   17. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
impl<S: OrderSide, T: OrderMatchType> FrameworkEval for MatchEval<S, T> {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let op = Instruction::<E::F>::from_eval(&mut eval);

        // is_real must be a boolean
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));

        // match leaf must be active
        eval.add_constraint(E::F::one() - op.leaf[LeafColumn::ACTIVE].clone());

        let mult = E::EF::from(op.is_real.clone());

        match T::MATCHTYPE {
            MatchType::Aggressive => {
                // opcode must be equal to the instruction's opcode
                eval.add_constraint(
                    op.opcode.clone() - E::F::from(S::op_code(IMTOperation::MatchAggressive)),
                );
                //@todo prev op must be insert S::Side
                let price: [E::F; N_U64_FELTS] =
                    array::from_fn(|i| op.leaf[LeafColumn::PRICE + i].clone());

                let (trade_price, less_than_values): ([E::F; N_U64_FELTS], Vec<E::F>) =
                    match S::SIDE {
                        Side::Buy => {
                            // opcode must be equal to the instruction's opcode
                            let trade_price =
                                array::from_fn(|i| op.initial_state.best_sell_price[i].clone());
                            let values = chain!(
                                trade_price.iter().cloned(),
                                price.iter().cloned(),
                                [E::F::one()]
                            )
                            .collect_vec();
                            (trade_price, values)
                        }
                        Side::Sell => {
                            let trade_price =
                                array::from_fn(|i| op.initial_state.best_buy_price[i].clone());
                            let values = chain!(
                                price.iter().cloned(),
                                trade_price.iter().cloned(),
                                [E::F::one()]
                            )
                            .collect_vec();
                            (trade_price, values)
                        }
                    };

                eval.add_to_relation(RelationEntry::new(
                    &self.less_than_elements,
                    mult.clone(),
                    &less_than_values,
                ));

                let volume: [E::F; N_U64_FELTS] =
                    array::from_fn(|i| op.leaf[LeafColumn::VOLUME + i].clone());
                let values = chain!(trade_price.into_iter(), volume.into_iter()).collect_vec();
                eval.add_to_relation(RelationEntry::new(
                    &self.match_elements,
                    -mult.clone(),
                    &values,
                ));
            }
            MatchType::Passive => {
                // opcode must be equal to the instruction's opcode
                eval.add_constraint(
                    op.opcode.clone() - E::F::from(S::op_code(IMTOperation::MatchPassive)),
                );

                //@todo prev op must be aggressive match S::side
                let price: [E::F; N_U64_FELTS] =
                    array::from_fn(|i| op.leaf[LeafColumn::PRICE + i].clone());
                let volume: [E::F; N_U64_FELTS] =
                    array::from_fn(|i| op.leaf[LeafColumn::VOLUME + i].clone());
                let values = chain!(price.into_iter(), volume.into_iter()).collect_vec();
                eval.add_to_relation(RelationEntry::new(
                    &self.match_elements,
                    mult.clone(),
                    &values,
                ));
            }
        }

        // Can we construct the entire low leaf here? and potentially reduce the number of constraints
        // ensure that the low leaf is the first leaf
        // low_leaf's next must point to leaf
        let first_price_time_felts = Leaf::<E::F, S>::first_price_time_felts();
        // assert active is set to 1
        eval.add_constraint(E::F::one() - op.low_leaf[0].clone());
        // assert volume must be zero
        for i in 0..N_U64_FELTS {
            eval.add_constraint(op.low_leaf[LeafColumn::VOLUME + i].clone());
        }
        // assert leaf's price_time is equal to the first price_time
        for i in 0..2 * N_U64_FELTS {
            eval.add_constraint(
                first_price_time_felts[i].clone() - op.low_leaf[LeafColumn::PRICE + i].clone(),
            );
        }
        // assert low leaf's next is equal to leaf's next
        for i in 0..2 * N_U64_FELTS {
            eval.add_constraint(
                op.leaf[LeafColumn::PRICE + i].clone() - op.low_leaf[LeafColumn::NEXT + i].clone(),
            );
        }

        // assert initial state root
        match S::side() {
            Side::Buy => {
                // initial state's buy root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.buy_root[i].clone()
                            - op.low_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
            }
            Side::Sell => {
                // initial state's sell root hash must be equal to the root hash of the merkle tree
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.initial_state.sell_root[i].clone()
                            - op.low_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }
            }
        }

        // eval low leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.low_merkle_path.clone(),
            op.low_leaf.clone(),
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // low leaf will now point to next highest priority
        let mut updated_low_leaf = op.low_leaf.clone();
        updated_low_leaf[LeafColumn::NEXT..N_LEAF_FELTS]
            .clone_from_slice(&op.leaf[LeafColumn::NEXT..N_LEAF_FELTS]);

        // eval updated low leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.low_merkle_proof.clone(),
            op.updated_low_merkle_path.clone(),
            updated_low_leaf,
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // the resultant root hash from updating low_leaf must be equal the path of matched leaf
        // this ensures that both leaf updates are consistent
        for i in 0..N_HASH {
            eval.add_constraint(
                op.updated_low_merkle_path[MERKLE_HEIGHT][i].clone()
                    - op.merkle_path[MERKLE_HEIGHT][i].clone(),
            );
        }

        // eval matched leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.merkle_path.clone(),
            op.leaf.clone(),
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // updates matched leaf active flag to 0
        let mut updated_leaf = op.leaf.clone();
        updated_leaf[LeafColumn::ACTIVE] = E::F::zero();

        // eval updated leaf's merkle proof
        eval_merkle_proof(
            &mut eval,
            op.merkle_proof.clone(),
            op.updated_merkle_path.clone(),
            updated_leaf,
            op.index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // ensure that the state count is updated correctly
        eval.add_constraint(op.final_state.n.clone() - op.initial_state.n.clone() - E::F::one());
        match S::side() {
            Side::Buy => {
                // final state's buy root hash must be equal to the root in the matched leaf's updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.buy_root[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the initial priority for sell IMT must be equal to the final priority
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.best_sell_price[i].clone()
                            - op.final_state.best_sell_price[i].clone(),
                    );
                }

                // the final root hash for sell IMT must be equal to the initial root hash
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.sell_root[i].clone() - op.initial_state.sell_root[i].clone(),
                    );
                }

                // the final priority will be equal to matched leaf's next price_time
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.final_state.best_buy_price[i].clone()
                            - op.leaf[LeafColumn::NEXT_PRICE + i].clone(),
                    );
                }
            }
            Side::Sell => {
                // initial state's sell root hash must be equal to the root in the matched leaf's updated merkle path
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.sell_root[i].clone()
                            - op.updated_merkle_path[MERKLE_HEIGHT][i].clone(),
                    );
                }

                // the initial priority for buy IMT must be equal to the final priority
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.initial_state.best_buy_price[i].clone()
                            - op.final_state.best_buy_price[i].clone(),
                    );
                }

                // the final root hash for buy IMT must be equal to the initial root hash
                for i in 0..N_HASH {
                    eval.add_constraint(
                        op.final_state.buy_root[i].clone() - op.initial_state.buy_root[i].clone(),
                    );
                }

                // the final priority will be equal to matched leaf's next price_time
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.final_state.best_sell_price[i].clone()
                            - op.leaf[LeafColumn::NEXT_PRICE + i].clone(),
                    );
                }
            }
        }

        let values: Vec<E::F> = flatten!(
            op.initial_state.n,
            op.initial_state.buy_root,
            op.initial_state.best_buy_price,
            op.initial_state.sell_root,
            op.initial_state.best_sell_price,
            op.opcode,
            op.low_merkle_proof,
            op.low_merkle_path,
            op.updated_low_merkle_path,
            op.low_index,
            op.low_leaf,
            op.merkle_proof,
            op.merkle_path,
            op.updated_merkle_path,
            op.index,
            op.leaf,
            op.final_state.n,
            op.final_state.buy_root,
            op.final_state.best_buy_price,
            op.final_state.sell_root,
            op.final_state.best_sell_price,
            op.is_real
        );
        // yield the results
        eval.add_to_relation(RelationEntry::new(
            &self.instruction_elements,
            -mult,
            &values,
        ));
        eval.finalize_logup();
        eval
    }
}

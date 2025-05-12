use crate::{
    components::{addition::AddElements, constraints_utils::eval_merkle_proof},
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
    components::{
        less_than::LessThanElements, order_match::MatchElements, poseidon::PoseidonElements, Claim,
    },
    executor::instruction::{Instruction, InstructionElements},
    flatten,
    hash::N_HASH,
    imt::{
        leaf::LeafColumn,
        side::{OrderSide, Side},
        MERKLE_HEIGHT, N_U64_FELTS,
    },
};

use super::PartialMatchColumn;

#[derive(Clone)]
pub struct PartialMatchEval<S, T: OrderMatchType> {
    pub claim: Claim<PartialMatchColumn<T>>,
    pub poseidon_elements: PoseidonElements,
    pub less_than_elements: LessThanElements,
    pub instruction_elements: InstructionElements,
    pub match_elements: MatchElements,
    pub add_elements: AddElements,
    pub _side: PhantomData<S>,
    pub _type: PhantomData<T>,
}

/// This implementation of the `FrameworkEval` trait for `PartialMatchEval` provides methods to evaluate
/// constraints on Partial Order Matches to Buy and Sell IMT;
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
///  1) Check if the low leaf points to the matched leaf.
///  2) Update the Volume of the Matched Leaf.
///  The constraints must ensure that the low leaf in the instruction is the first leaf in the tree.
///  The constraints must ensure that the updates are done correctly.
///
///   The method follows these steps:
///   1. Retrieve Instruction for the row
///   2. IsReal must be a boolean. it is true if the operation is from non-padded row.
///   3. The Matched Leaf must be active.
///   4. Assert that the opcode is equal to the operation's opcode. // different for side + type combination
///   5. Todo constraint:- The Op code that precedes the current operation must be correct.
///        - Aggressive Match: The previous operation must be an insert operation on the same side.
///        - Passive Match: The previous operation must be an aggressive match operation on the opposite side.
///          Note - The previous operation can be either full or partial match.
///   6. Check For the Match Invairant:(This Check is only for Aggressive Match)
///      - Invariant: MAX(buy_imt) >= MIN(sell_imt)
///      - On Buy Side: leaf.price >= initial_state.best_sell_price(trade_price), less_than_values [trade_price, leaf.price, 1]
///      - On Sell Side: leaf.price <= initial_state.best_buy_price(trade_price), less_than_values [leaf.price, trade_price, 1]
///      - The Match Elements are yielded, Match Elements consist of (price, volume) pair.
///      - Todo: This must contain the side of the aggressive side, like 0/1
///      - Todo: This must contain Trade_ID
///   7. Use The Match Elements:(This Check is only for Passive Match)
///      - Since the trade_price is always set by the passive side, the leaf price, volume = filled_volume
///   8. The Remaining Voume + Filled Volume must be equal to the initial volume.
///   9. Construct the low leaf, from the first price_time felts, and the next to be matched leaf's label.
///   10. Assert that the low index is 0.
///   11. Assert that the initial root hash of the initial state is equal to the root hash in the merkle path of the low/0th leaf.
///   12. The Low leaf is part of the Merkle Tree by verifying the Merkle Proof.
///      - The Merkle Proof is a list of sibling hashes from the leaf to the root.
///      - The Merkle Path is a list of hashes from the leaf to the root.
///      - IndexBits is the binary representation of the index of the leaf.
///   13. Ensure that the root hash in low leaf's merkle path is equal to the root contained in matched leaf's merkle path.
///   14. Verify the Merkle Proof of the Matched Leaf.
///   15. Update the Matched Leaf's volume to remaining volume.
///   16. Ensure that the final state's count is equal to the initial state's count + 1.
///   17. Ensure that the resulting root hash from update of matched leaf's is equal to the final state's root hash.
///   18. Ensure That the final state values for the other side of the tree are same as the initial state values.
///   19. Ensure that the final state's priority remains the same.
///   20. Yield the Results by adding the values to the ProcessorLookupElements.   
///        - Multiplicity of the relation is positive of is_real flag.
///        - Values is the entire row of the trace table.
///   21. Finalize the evaluation by calling `eval.finalize_logup_in_pairs()`.
///
impl<S: OrderSide, T: OrderMatchType> FrameworkEval for PartialMatchEval<S, T> {
    /// Returns the log size parameter from the claim.
    ///
    /// # Examples
    ///
    /// ```
    /// let eval = PartialMatchEval { claim: claim_struct, /* other fields */ };
    /// let log_size = eval.log_size();
    /// assert_eq!(log_size, claim_struct.log_size);
    /// ```
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }
    /// Returns the maximum log degree bound for constraints as the claim's log size plus one.
    ///
    /// # Examples
    ///
    /// ```
    /// let eval = PartialMatchEval { claim: Claim { log_size: 4, /* ... */ }, /* ... */ };
    /// assert_eq!(eval.max_constraint_log_degree_bound(), 5);
    /// ```
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.claim.log_size + 1
    }
    /// Evaluates all constraints for a partial order match operation in an Incremental Merkle Tree (IMT).
    ///
    /// This method enforces the correctness of a partial match (aggressive or passive) on either the buy or sell side,
    /// ensuring state transitions, Merkle proofs, volume updates, and opcode consistency are valid within the IMT-based order book.
    /// It checks boolean flags, verifies Merkle proofs for both the matched and constructed leaves, enforces volume conservation,
    /// and ensures the integrity of root hashes and priority values for both sides of the order book.
    ///
    /// # Type Parameters
    /// - `E`: The evaluation context implementing `EvalAtRow`.
    ///
    /// # Returns
    /// The updated evaluation context after all constraints have been applied.
    ///
    /// # Examples
    ///
    /// ```
    /// // Assume `eval` is an evaluation context and `partial_match_eval` is an instance of PartialMatchEval.
    /// let updated_eval = partial_match_eval.evaluate(eval);
    /// ```
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let op = Instruction::<E::F>::from_eval(&mut eval);

        // is_real must be a boolean
        eval.add_constraint(op.is_real.clone() * (op.is_real.clone() - E::F::one()));

        // match leaf must be active
        eval.add_constraint(E::F::one() - op.leaf[LeafColumn::ACTIVE].clone());

        let mult = E::EF::from(op.is_real.clone());

        // extract filled volume and remaining volume contained in the instruction's low leaf
        let filled_volume: [E::F; N_U64_FELTS] = array::from_fn(|i| op.low_leaf[i].clone());

        let remaining_volume: [E::F; N_U64_FELTS] =
            array::from_fn(|i| op.low_leaf[N_U64_FELTS + i].clone());
        match T::MATCHTYPE {
            MatchType::Aggressive => {
                // opcode must be equal to the instruction's opcode
                eval.add_constraint(
                    op.opcode.clone()
                        - E::F::from(S::op_code(IMTOperation::PartialMatchAggressive)),
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

                let values = chain!(trade_price.into_iter(), filled_volume.clone().into_iter())
                    .collect_vec();
                eval.add_to_relation(RelationEntry::new(
                    &self.match_elements,
                    -mult.clone(),
                    &values,
                ));
            }
            MatchType::Passive => {
                // opcode must be equal to the instruction's opcode
                eval.add_constraint(
                    op.opcode.clone() - E::F::from(S::op_code(IMTOperation::PartialMatchPassive)),
                );

                //@todo prev op must be aggressive match S::side
                let price: [E::F; N_U64_FELTS] =
                    array::from_fn(|i| op.leaf[LeafColumn::PRICE + i].clone());
                let values =
                    chain!(price.into_iter(), filled_volume.clone().into_iter()).collect_vec();
                eval.add_to_relation(RelationEntry::new(
                    &self.match_elements,
                    mult.clone(),
                    &values,
                ));
            }
        }

        // remaining volume + filled volume must be equal to the initial volume
        let add_elements = chain!(
            filled_volume.iter().cloned(),
            remaining_volume.iter().cloned(),
            op.leaf[LeafColumn::VOLUME..LeafColumn::PRICE]
                .iter()
                .cloned()
        )
        .collect_vec();
        eval.add_to_relation(RelationEntry::new(
            &self.add_elements,
            mult.clone(),
            &add_elements,
        ));

        let mut low_leaf: [E::F; N_LEAF_FELTS] = array::from_fn(|_| E::F::zero());
        low_leaf[LeafColumn::ACTIVE] = E::F::one();
        let first_price_time_felts = Leaf::<E::F, S>::first_price_time_felts();
        for i in 0..2 * N_U64_FELTS {
            low_leaf[LeafColumn::LABEL + i] = first_price_time_felts[i].clone();
        }
        for i in 0..2 * N_U64_FELTS {
            low_leaf[LeafColumn::NEXT + i] = op.leaf[LeafColumn::LABEL + i].clone();
        }

        // low index must be 0
        for i in 0..MERKLE_HEIGHT {
            eval.add_constraint(op.low_index[i].clone());
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
            low_leaf.clone(),
            op.low_index.clone(),
            &self.poseidon_elements,
            mult.clone(),
        );

        // the root hash from low leaf's merkle path must be equal the path of matched leaf
        for i in 0..N_HASH {
            eval.add_constraint(
                op.low_merkle_path[MERKLE_HEIGHT][i].clone()
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
        for i in 0..N_U64_FELTS {
            updated_leaf[LeafColumn::VOLUME + i] = remaining_volume[i].clone();
        }

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

                // the final priority of the buy side remains the same.
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.final_state.best_buy_price[i].clone()
                            - op.initial_state.best_buy_price[i].clone(),
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

                // the final priority of the sell side remains the same.
                for i in 0..N_U64_FELTS {
                    eval.add_constraint(
                        op.final_state.best_sell_price[i].clone()
                            - op.initial_state.best_sell_price[i].clone(),
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

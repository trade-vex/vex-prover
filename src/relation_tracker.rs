use std::marker::PhantomData;

use itertools::Itertools;
use stwo_prover::constraint_framework::relation_tracker::{
    RelationSummary, RelationTrackerComponent,
};
use stwo_prover::constraint_framework::TraceLocationAllocator;
use stwo_prover::core::backend::simd::SimdBackend;
use stwo_prover::core::backend::BackendForChannel;
use stwo_prover::core::channel::MerkleChannel;
use stwo_prover::core::pcs::CommitmentSchemeProver;
use stwo_prover::core::poly::circle::CanonicCoset;
use tracing::info;

use crate::components::bytes::{AndElements, BytesEval, LessThanU8Elements, RangeCheckU8Elements};
use crate::components::insertions::InsertionsEval;
use crate::components::less_than::{LessThanElements, LessThanEval, StrictLessThanElements};
use crate::components::order_match::{MatchElements, MatchEval};
use crate::components::poseidon::{PoseidonElements, PoseidonEval};
use crate::components::processor::ProcessorEval;
use crate::executor::instruction::InstructionElements;
use crate::executor::state::StateElements;
use crate::imt::side::{Aggressive, Buy, Passive, Sell};
use crate::VexClaim;

pub fn track_vex_relations<MC: MerkleChannel>(
    commitment_scheme: &CommitmentSchemeProver<'_, SimdBackend, MC>,
    claim: &VexClaim,
) where
    SimdBackend: BackendForChannel<MC>,
{
    let evals = commitment_scheme.trace().polys.map(|interaction_tree| {
        interaction_tree
            .iter()
            .map(|poly| poly.evaluate(CanonicCoset::new(poly.log_size()).circle_domain()))
            .collect_vec()
    });
    let evals = &evals.as_ref();
    let trace = &evals.into();

    let tree_span_provider = &mut TraceLocationAllocator::default();
    let mut entries = vec![];

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            BytesEval {
                claim: claim.bytes_claim.clone(),
                and_elements: AndElements::dummy(),
                less_than_u8_elements: LessThanU8Elements::dummy(),
                range_check_u8_elements: RangeCheckU8Elements::dummy(),
            },
            1 << claim.bytes_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            PoseidonEval {
                claim: claim.poseidon_claim.clone(),
                poseidon_elements: PoseidonElements::dummy(),
            },
            1 << claim.poseidon_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            LessThanEval::<true> {
                claim: claim.strict_less_than_claim.clone(),
                less_than_elements: LessThanElements::dummy(),
                strict_less_than_elements: StrictLessThanElements::dummy(),
                less_than_u8_elements: LessThanU8Elements::dummy(),
            },
            1 << claim.strict_less_than_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            LessThanEval::<false> {
                claim: claim.less_than_claim.clone(),
                less_than_elements: LessThanElements::dummy(),
                strict_less_than_elements: StrictLessThanElements::dummy(),
                less_than_u8_elements: LessThanU8Elements::dummy(),
            },
            1 << claim.less_than_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            ProcessorEval {
                claim: claim.processor_claim.clone(),
                instruction_elements: InstructionElements::dummy(),
                state_elements: StateElements::dummy(),
            },
            1 << claim.processor_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            InsertionsEval {
                claim: claim.buy_insert_claim.clone(),
                instruction_elements: InstructionElements::dummy(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                strict_less_than_elements: StrictLessThanElements::dummy(),
                _side: PhantomData::<Buy>,
            },
            1 << claim.buy_insert_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            InsertionsEval {
                claim: claim.sell_insert_claim.clone(),
                instruction_elements: InstructionElements::dummy(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                strict_less_than_elements: StrictLessThanElements::dummy(),
                _side: PhantomData::<Sell>,
            },
            1 << claim.sell_insert_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.buy_aggressive_match_claim.clone(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                match_elements: MatchElements::dummy(),
                instruction_elements: InstructionElements::dummy(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Aggressive>,
            },
            1 << claim.buy_aggressive_match_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.sell_aggressive_match_claim.clone(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                match_elements: MatchElements::dummy(),
                instruction_elements: InstructionElements::dummy(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Aggressive>,
            },
            1 << claim.sell_aggressive_match_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.buy_passive_match_claim.clone(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                match_elements: MatchElements::dummy(),
                instruction_elements: InstructionElements::dummy(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Passive>,
            },
            1 << claim.buy_passive_match_claim.log_size,
        )
        .entries(trace),
    );

    entries.extend(
        RelationTrackerComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.sell_passive_match_claim.clone(),
                poseidon_elements: PoseidonElements::dummy(),
                less_than_elements: LessThanElements::dummy(),
                match_elements: MatchElements::dummy(),
                instruction_elements: InstructionElements::dummy(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Passive>,
            },
            1 << claim.sell_passive_match_claim.log_size,
        )
        .entries(trace),
    );

    info!(
        "Relation Summary: {:?}",
        RelationSummary::summarize_relations(&entries).cleaned()
    );
}

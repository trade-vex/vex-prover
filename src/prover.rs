use num_traits::Zero;
use stwo_prover::{
    constraint_framework::{
        Relation, INTERACTION_TRACE_IDX, ORIGINAL_TRACE_IDX, PREPROCESSED_TRACE_IDX,
    },
    core::{
        backend::simd::SimdBackend,
        channel::Blake2sChannel,
        fields::{m31::BaseField, qm31::SecureField, FieldExpOps},
        pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig},
        poly::circle::{CanonicCoset, PolyOps},
        prover::{self, verify, ProvingError, VerificationError},
        vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher},
    },
};
use tracing::{span, Level};

use crate::{
    components::{
        bytes, insertions, is_first, less_than, poseidon, processor, VexComponent, VexComponents,
        VexInteractionElements,
    },
    executor::record::ExecutionTrace,
    imt::side::{Buy, Sell},
    VexClaim, VexInteractionClaim, VexProof,
};

/// Prove the Vex Execution Trace
pub fn prove_vex(
    trace: ExecutionTrace<BaseField>,
) -> Result<VexProof<Blake2sMerkleHasher>, ProvingError> {
    let _span = span!(Level::INFO, "Prove Vex").entered();

    // default config
    let config = PcsConfig::default();

    // precompute twiddles for low degree polynomial extension
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(trace.max_log_size() + config.fri_config.log_blowup_factor + 2)
            .circle_domain()
            .half_coset,
    );

    // blake2s channel and commitment scheme used in merkle tree
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let span = span!(Level::INFO, "Preprocessed Trace").entered();
    let mut tree_builder = commitment_scheme.tree_builder();

    // Extend the preprocessed trace with the components
    tree_builder.extend_evals(bytes::preprocessed_trace());
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::Poseidon)));
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::StrictLessThan)));
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::LessThan)));
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::Processor)));
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::InsertBuyOrder)));
    tree_builder.extend_evals(is_first(trace.log_size(VexComponent::InsertSellOrder)));
    tree_builder.commit(channel);
    span.exit();

    let span = span!(Level::INFO, "Main Trace").entered();
    let mut tree_builder = commitment_scheme.tree_builder();
    let (bytes_trace, bytes_claim) = bytes::trace(trace.byte_operations.clone());
    let (poseidon_trace, poseidon_claim) = poseidon::trace(trace.poseidon_operations);
    let (strict_less_than_trace, strict_less_than_claim) =
        less_than::trace_eval::<true>(trace.strict_less_than_operations);
    let (less_than_trace, less_than_claim) =
        less_than::trace_eval::<false>(trace.less_than_operations);
    let (processor_trace, processor_claim) = processor::trace(trace.instructions);
    let (buy_insert_trace, buy_insert_claim) = insertions::trace::<Buy>(trace.buy_insert_order);
    let (sell_insert_trace, sell_insert_claim) = insertions::trace::<Sell>(trace.sell_insert_order);

    // Extend the main trace with the components
    tree_builder.extend_evals(bytes_trace);
    tree_builder.extend_evals(poseidon_trace.clone());
    tree_builder.extend_evals(strict_less_than_trace.clone());
    tree_builder.extend_evals(less_than_trace.clone());
    tree_builder.extend_evals(processor_trace.clone());
    tree_builder.extend_evals(buy_insert_trace.clone());
    tree_builder.extend_evals(sell_insert_trace.clone());

    // create the VexClaim
    let claim = VexClaim {
        final_state: trace.final_state,
        initial_state: trace.initial_state,
        processor_claim,
        buy_insert_claim,
        sell_insert_claim,
        poseidon_claim,
        strict_less_than_claim,
        less_than_claim,
        bytes_claim,
    };

    // Mix the claim into the channel.
    claim.mix_into(channel);
    // Commit the main trace.
    tree_builder.commit(channel);
    span.exit();

    let span = span!(Level::INFO, "Interaction Trace").entered();

    // Draw interaction elements
    let interaction_elements = VexInteractionElements::draw(channel);

    let mut tree_builder = commitment_scheme.tree_builder();
    let (bytes_interaction_trace, bytes_interaction_claim) = bytes::interaction_trace(
        trace.byte_operations,
        &interaction_elements.and_elements,
        &interaction_elements.less_than_u8_elements,
        &interaction_elements.range_check_u8_elements,
    );
    let (poseidon_interaction_trace, poseidon_interaction_claim) =
        poseidon::interaction_trace(&poseidon_trace, &interaction_elements.poseidon_elements);
    let (processor_interaction_trace, processor_interaction_claim) = processor::interaction_trace(
        &processor_trace,
        &interaction_elements.state_elements,
        &interaction_elements.instruction_elements,
    );
    let (strict_less_than_interaction_trace, strict_less_than_interaction_claim) =
        less_than::interaction_trace_eval::<true, _>(
            &strict_less_than_trace,
            &interaction_elements.less_than_u8_elements,
            &interaction_elements.strict_less_than_elements,
        );
    let (less_than_interaction_trace, less_than_interaction_claim) =
        less_than::interaction_trace_eval::<false, _>(
            &less_than_trace,
            &interaction_elements.less_than_u8_elements,
            &interaction_elements.less_than_elements,
        );
    let (buy_insert_interaction_trace, buy_insert_interaction_claim) =
        insertions::interaction_trace::<Buy>(
            &buy_insert_trace,
            &interaction_elements.poseidon_elements,
            &interaction_elements.less_than_elements,
            &interaction_elements.strict_less_than_elements,
            &interaction_elements.instruction_elements,
        );
    let (sell_insert_interaction_trace, sell_insert_interaction_claim) =
        insertions::interaction_trace::<Sell>(
            &sell_insert_trace,
            &interaction_elements.poseidon_elements,
            &interaction_elements.less_than_elements,
            &interaction_elements.strict_less_than_elements,
            &interaction_elements.instruction_elements,
        );

    tree_builder.extend_evals(bytes_interaction_trace);
    tree_builder.extend_evals(poseidon_interaction_trace);
    tree_builder.extend_evals(strict_less_than_interaction_trace);
    tree_builder.extend_evals(less_than_interaction_trace);
    tree_builder.extend_evals(processor_interaction_trace);
    tree_builder.extend_evals(buy_insert_interaction_trace);
    tree_builder.extend_evals(sell_insert_interaction_trace);

    let interaction_claim = VexInteractionClaim {
        processor_interaction_claim,
        buy_insert_interaction_claim,
        sell_insert_interaction_claim,
        poseidon_interaction_claim,
        strict_less_than_interaction_claim,
        less_than_interaction_claim,
        bytes_interaction_claim,
    };

    // Mix the interaction claim into the channel.
    interaction_claim.mix_into(channel);

    // Commit interaction trace.
    tree_builder.commit(channel);
    span.exit();

    let span = span!(Level::INFO, "Proof Generation").entered();
    let component_builder = VexComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.provers();
    let proof = prover::prove::<SimdBackend, _>(&components, channel, commitment_scheme)?;
    span.exit();

    Ok(VexProof {
        claim,
        interaction_claim,
        stark_proof: proof,
    })
}

/// Verify VexProof
pub fn verify_vex(
    VexProof {
        claim,
        interaction_claim,
        stark_proof,
    }: VexProof<Blake2sMerkleHasher>,
) -> Result<(), VerificationError> {
    let _span = span!(Level::INFO, "Verify").entered();

    // default config
    let config = PcsConfig::default();
    let channel = &mut Blake2sChannel::default();
    let commitment_scheme_verifier =
        &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
    let log_sizes = &claim.log_sizes();

    // preprocessed trace
    commitment_scheme_verifier.commit(
        stark_proof.commitments[PREPROCESSED_TRACE_IDX],
        &log_sizes[PREPROCESSED_TRACE_IDX],
        channel,
    );

    // main trace
    claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        stark_proof.commitments[ORIGINAL_TRACE_IDX],
        &log_sizes[ORIGINAL_TRACE_IDX],
        channel,
    );

    // interaction trace
    let interaction_elements = VexInteractionElements::draw(channel);
    let initial_state_comb: SecureField = interaction_elements
        .state_elements
        .combine(&claim.initial_state);
    let final_state_comb: SecureField = interaction_elements
        .state_elements
        .combine(&claim.final_state);
    // Check that the lookup sum is valid, otherwise throw
    if !(interaction_claim.logup_sum() + final_state_comb.inverse() - initial_state_comb.inverse())
        .is_zero()
    {
        return Err(VerificationError::ProofOfWork);
    };
    interaction_claim.mix_into(channel);
    commitment_scheme_verifier.commit(
        stark_proof.commitments[INTERACTION_TRACE_IDX],
        &log_sizes[INTERACTION_TRACE_IDX],
        channel,
    );

    // Verify the proof
    let component_builder = VexComponents::new(&claim, &interaction_elements, &interaction_claim);
    let components = component_builder.components();

    verify(
        &components,
        channel,
        commitment_scheme_verifier,
        stark_proof,
    )
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use rand::Rng;
    use tracing::{span, Level};

    use crate::{
        executor::{order_book::OrderBook, record::ExecutionTrace},
        imt::order::Order,
    };

    use super::*;

    #[test_log::test]
    fn test_prove() {
        // Execution Record
        let span = span!(Level::INFO, "Generating Execution Record").entered();
        let record = Rc::new(RefCell::new(ExecutionTrace::new()));
        let mut order_book = OrderBook::new(Rc::clone(&record));
        let mut rng = rand::thread_rng();
        let mut time = 1;
        let n = 1 << 8;
        for _ in 0..n {
            let time_inc = rng.gen_range(1..=16);
            time += time_inc;
            let buy_order = Order::new(rng.gen_range(1..=50), rng.gen_range(51..=100), time);
            let sell_order = Order::new(rng.gen_range(101..=150), rng.gen_range(151..=200), time);
            order_book.place_buy_order(buy_order).unwrap();
            order_book.place_sell_order(sell_order).unwrap();
        }

        let mut execution_trace =
            std::mem::replace(&mut *record.borrow_mut(), ExecutionTrace::new());
        execution_trace.final_state = order_book.state().to_felts();
        span.exit();
        let proof = prove_vex(execution_trace).unwrap();
        verify_vex(proof).unwrap();
    }
}

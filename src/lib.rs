#![feature(btree_cursors, portable_simd, iter_array_chunks)]
#![feature(trait_upcasting)]

#[cfg(feature = "jemalloc")]
use tikv_jemallocator::Jemalloc;
#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use crate::executor::state::StateFelts;
use components::{
    addition::AddColumn, bytes::BytesPreProcessedColumn, insertions::InsertionsColumn,
    less_than::LessThanColumn, order_match::MatchColumn, partial_order_match::PartialMatchColumn,
    poseidon::PoseidonColumn, processor::ProcessorColumn, Claim, InteractionClaim,
};
use executor::state::StateElements;
use imt::side::{Aggressive, Passive};
use num_traits::Zero;
use stwo_prover::{
    constraint_framework::Relation,
    core::{
        channel::Channel,
        fields::{m31::BaseField, qm31::SecureField, FieldExpOps},
        pcs::TreeVec,
        prover::StarkProof,
        vcs::ops::MerkleHasher,
    },
};

pub mod components;
pub mod constants;
pub mod error;
pub mod executor;
pub mod hash;
pub mod imt;
pub mod prover;
#[cfg(feature = "relation-tracker")]
pub mod relation_tracker;
pub mod types;

#[derive(Debug)]
pub struct VexProof<H: MerkleHasher> {
    pub stark_proof: StarkProof<H>,
    pub claim: VexClaim,
    pub interaction_claim: VexInteractionClaim,
}

/// Claim for the Vex Prover
/// Claim containts public inputs, initial state, final state and all the components
/// and LogSizes for each component
pub struct VexClaim {
    /// The Initial State of the Matching Engine
    pub initial_state: StateFelts<BaseField>,
    /// The Final State of the Matching Engine
    pub final_state: StateFelts<BaseField>,
    /// processor claim
    pub processor_claim: Claim<ProcessorColumn>,
    /// buy insert claim
    pub buy_insert_claim: Claim<InsertionsColumn>,
    /// sell insert claim
    pub sell_insert_claim: Claim<InsertionsColumn>,
    /// poseidon claim
    pub poseidon_claim: Claim<PoseidonColumn>,
    /// strictly less than claim
    pub strict_less_than_claim: Claim<LessThanColumn>,
    /// less than claim
    pub less_than_claim: Claim<LessThanColumn>,
    /// add claim
    pub add_claim: Claim<AddColumn>,
    /// bytes component claim
    pub bytes_claim: Claim<BytesPreProcessedColumn>,
    /// Buy Aggressive Match Claim
    pub buy_aggressive_match_claim: Claim<MatchColumn<Aggressive>>,
    /// Sell Aggressive Match Claim
    pub sell_aggressive_match_claim: Claim<MatchColumn<Aggressive>>,
    /// Buy Passive Match Claim
    pub buy_passive_match_claim: Claim<MatchColumn<Passive>>,
    /// Sell Passive Match Claim
    pub sell_passive_match_claim: Claim<MatchColumn<Passive>>,
    /// Buy Aggressive Partial Match Claim
    pub buy_aggressive_partial_match_claim: Claim<PartialMatchColumn<Aggressive>>,
    /// Sell Aggressive Partial Match Claim
    pub sell_aggressive_partial_match_claim: Claim<PartialMatchColumn<Aggressive>>,
    /// Buy Passive Partial Match Claim
    pub buy_passive_partial_match_claim: Claim<PartialMatchColumn<Passive>>,
    /// Sell Passive Partial Match Claim
    pub sell_passive_partial_match_claim: Claim<PartialMatchColumn<Passive>>,
}

impl VexClaim {
    /// mix all components log sizes and public inputs into the channel
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.bytes_claim.mix_into(channel);
        self.poseidon_claim.mix_into(channel);
        // strict_less_than is unified into less_than, but keep in mix for now
        self.strict_less_than_claim.mix_into(channel);
        self.less_than_claim.mix_into(channel);
        self.add_claim.mix_into(channel);
        self.processor_claim.mix_into(channel);
        self.buy_insert_claim.mix_into(channel);
        self.sell_insert_claim.mix_into(channel);
        self.buy_aggressive_match_claim.mix_into(channel);
        self.sell_aggressive_match_claim.mix_into(channel);
        self.buy_passive_match_claim.mix_into(channel);
        self.sell_passive_match_claim.mix_into(channel);
        self.buy_aggressive_partial_match_claim.mix_into(channel);
        self.sell_aggressive_partial_match_claim.mix_into(channel);
        self.buy_passive_partial_match_claim.mix_into(channel);
        self.sell_passive_partial_match_claim.mix_into(channel);
    }

    /// Returns the total log size of all components
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::concat_cols(
            [
                self.bytes_claim.log_sizes(),
                self.poseidon_claim.log_sizes(),
                // strict_less_than is unified into less_than, but keep in log_sizes for now
                self.strict_less_than_claim.log_sizes(),
                self.less_than_claim.log_sizes(),
                self.add_claim.log_sizes(),
                self.processor_claim.log_sizes(),
                self.buy_insert_claim.log_sizes(),
                self.sell_insert_claim.log_sizes(),
                self.buy_aggressive_match_claim.log_sizes(),
                self.sell_aggressive_match_claim.log_sizes(),
                self.buy_passive_match_claim.log_sizes(),
                self.sell_passive_match_claim.log_sizes(),
                self.buy_aggressive_partial_match_claim.log_sizes(),
                self.sell_aggressive_partial_match_claim.log_sizes(),
                self.buy_passive_partial_match_claim.log_sizes(),
                self.sell_passive_partial_match_claim.log_sizes(),
            ]
            .into_iter(),
        )
    }
}

impl std::fmt::Debug for VexClaim {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VexClaim")
            .field("initial_state", &self.initial_state)
            .field("final_state", &self.final_state)
            .field("processor_log_size", &self.processor_claim.log_size)
            .field("buy_insert_log_size", &self.buy_insert_claim.log_size)
            .field("sell_insert_log_size", &self.sell_insert_claim.log_size)
            .field("poseidon_log_size", &self.poseidon_claim.log_size)
            .field(
                "strict_less_than_log_size",
                &self.strict_less_than_claim.log_size,
            )
            .field("less_than_log_size", &self.less_than_claim.log_size)
            .field("add_log_size", &self.add_claim.log_size)
            .field("bytes_log_size", &self.bytes_claim.log_size)
            .field(
                "buy_aggressive_match_log_size",
                &self.buy_aggressive_match_claim.log_size,
            )
            .field(
                "sell_aggressive_match_log_size",
                &self.sell_aggressive_match_claim.log_size,
            )
            .field(
                "buy_passive_match_log_size",
                &self.buy_passive_match_claim.log_size,
            )
            .field(
                "sell_passive_match_log_size",
                &self.sell_passive_match_claim.log_size,
            )
            .field(
                "buy_aggressive_partial_match_log_size",
                &self.buy_aggressive_partial_match_claim.log_size,
            )
            .field(
                "sell_aggressive_partial_match_log_size",
                &self.sell_aggressive_partial_match_claim.log_size,
            )
            .field(
                "buy_passive_partial_match_log_size",
                &self.buy_passive_partial_match_claim.log_size,
            )
            .field(
                "sell_passive_partial_match_log_size",
                &self.sell_passive_partial_match_claim.log_size,
            )
            .finish()
    }
}

/// Interaction Claim for the Vex Prover
/// Contains LogUp Sum for each component
pub struct VexInteractionClaim {
    /// Processor component interaction claim
    pub processor_interaction_claim: InteractionClaim<ProcessorColumn>,
    /// Buy insert component interaction claim
    pub buy_insert_interaction_claim: InteractionClaim<InsertionsColumn>,
    /// Sell insert component interaction claim
    pub sell_insert_interaction_claim: InteractionClaim<InsertionsColumn>,
    /// Poseidon component interaction claim
    pub poseidon_interaction_claim: InteractionClaim<PoseidonColumn>,
    /// Strictly less than component interaction claim
    pub strict_less_than_interaction_claim: InteractionClaim<LessThanColumn>,
    /// Less than component interaction claim
    pub less_than_interaction_claim: InteractionClaim<LessThanColumn>,
    /// Add component interaction claim
    pub add_interaction_claim: InteractionClaim<AddColumn>,
    /// Bytes component interaction claim
    pub bytes_interaction_claim: InteractionClaim<BytesPreProcessedColumn>,
    /// Buy Aggressive Match Interaction Claim
    pub buy_aggressive_match_interaction_claim: InteractionClaim<MatchColumn<Aggressive>>,
    /// Sell Aggressive Match Interaction Claim
    pub sell_aggressive_match_interaction_claim: InteractionClaim<MatchColumn<Aggressive>>,
    /// Buy Passive Match Interaction Claim
    pub buy_passive_match_interaction_claim: InteractionClaim<MatchColumn<Passive>>,
    /// Sell Passive Match Interaction Claim
    pub sell_passive_match_interaction_claim: InteractionClaim<MatchColumn<Passive>>,
    /// Buy Aggressive Partial Match Interaction Claim
    pub buy_aggressive_partial_match_interaction_claim:
        InteractionClaim<PartialMatchColumn<Aggressive>>,
    /// Sell Aggressive Partial Match Interaction Claim
    pub sell_aggressive_partial_match_interaction_claim:
        InteractionClaim<PartialMatchColumn<Aggressive>>,
    /// Buy Passive Partial Match Interaction Claim
    pub buy_passive_partial_match_interaction_claim: InteractionClaim<PartialMatchColumn<Passive>>,
    /// Sell Passive Partial Match Interaction Claim
    pub sell_passive_partial_match_interaction_claim: InteractionClaim<PartialMatchColumn<Passive>>,
}

impl VexInteractionClaim {
    /// mix all logups into the channel
    pub fn mix_into(&self, channel: &mut impl Channel) {
        self.bytes_interaction_claim.mix_into(channel);
        self.poseidon_interaction_claim.mix_into(channel);
        // Both claims use unified logic but are kept separate
        self.strict_less_than_interaction_claim.mix_into(channel);
        self.less_than_interaction_claim.mix_into(channel);
        self.add_interaction_claim.mix_into(channel);
        self.processor_interaction_claim.mix_into(channel);
        self.buy_insert_interaction_claim.mix_into(channel);
        self.sell_insert_interaction_claim.mix_into(channel);
        self.buy_aggressive_match_interaction_claim
            .mix_into(channel);
        self.sell_aggressive_match_interaction_claim
            .mix_into(channel);
        self.buy_passive_match_interaction_claim.mix_into(channel);
        self.sell_passive_match_interaction_claim.mix_into(channel);
        self.buy_aggressive_partial_match_interaction_claim
            .mix_into(channel);
        self.sell_aggressive_partial_match_interaction_claim
            .mix_into(channel);
        self.buy_passive_partial_match_interaction_claim
            .mix_into(channel);
        self.sell_passive_partial_match_interaction_claim
            .mix_into(channel);
    }

    /// Returns the total logup sum of all components
    fn components_logup_sum(&self) -> SecureField {
        let mut sum = SecureField::zero();
        sum += self.processor_interaction_claim.claimed_sum;
        sum += self.buy_insert_interaction_claim.claimed_sum;
        sum += self.sell_insert_interaction_claim.claimed_sum;
        sum += self.poseidon_interaction_claim.claimed_sum;
        sum += self.strict_less_than_interaction_claim.claimed_sum;
        sum += self.less_than_interaction_claim.claimed_sum;
        sum += self.add_interaction_claim.claimed_sum;
        sum += self.bytes_interaction_claim.claimed_sum;
        sum += self.buy_aggressive_match_interaction_claim.claimed_sum;
        sum += self.sell_aggressive_match_interaction_claim.claimed_sum;
        sum += self.buy_passive_match_interaction_claim.claimed_sum;
        sum += self.sell_passive_match_interaction_claim.claimed_sum;
        sum += self
            .buy_aggressive_partial_match_interaction_claim
            .claimed_sum;
        sum += self
            .sell_aggressive_partial_match_interaction_claim
            .claimed_sum;
        sum += self.buy_passive_partial_match_interaction_claim.claimed_sum;
        sum += self
            .sell_passive_partial_match_interaction_claim
            .claimed_sum;
        sum
    }

    /// Returns the logup sum of all components and yields the initial state and final state
    /// This Must be Zero if all the lookups were correct
    pub fn logup_sum(&self, claim: &VexClaim, state_elements: &StateElements) -> SecureField {
        let initial_state_comb: SecureField = state_elements.combine(&claim.initial_state);
        let final_state_comb: SecureField = state_elements.combine(&claim.final_state);
        self.components_logup_sum() + final_state_comb.inverse() - initial_state_comb.inverse()
    }
}

impl std::fmt::Debug for VexInteractionClaim {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VexInteractionClaim")
            .field("processor", &self.processor_interaction_claim.claimed_sum)
            .field("buy_insert", &self.buy_insert_interaction_claim.claimed_sum)
            .field(
                "sell_insert",
                &self.sell_insert_interaction_claim.claimed_sum,
            )
            .field("poseidon", &self.poseidon_interaction_claim.claimed_sum)
            .field(
                "strict_less_than",
                &self.strict_less_than_interaction_claim.claimed_sum,
            )
            .field("less_than", &self.less_than_interaction_claim.claimed_sum)
            .field("add", &self.add_interaction_claim.claimed_sum)
            .field("bytes", &self.bytes_interaction_claim.claimed_sum)
            .field(
                "buy_aggressive_match",
                &self.buy_aggressive_match_interaction_claim.claimed_sum,
            )
            .field(
                "sell_aggressive_match",
                &self.sell_aggressive_match_interaction_claim.claimed_sum,
            )
            .field(
                "buy_passive_match",
                &self.buy_passive_match_interaction_claim.claimed_sum,
            )
            .field(
                "sell_passive_match",
                &self.sell_passive_match_interaction_claim.claimed_sum,
            )
            .field(
                "buy_aggressive_partial_match",
                &self
                    .buy_aggressive_partial_match_interaction_claim
                    .claimed_sum,
            )
            .field(
                "sell_aggressive_partial_match",
                &self
                    .sell_aggressive_partial_match_interaction_claim
                    .claimed_sum,
            )
            .field(
                "buy_passive_partial_match",
                &self.buy_passive_partial_match_interaction_claim.claimed_sum,
            )
            .field(
                "sell_passive_partial_match",
                &self
                    .sell_passive_partial_match_interaction_claim
                    .claimed_sum,
            )
            .finish()
    }
}

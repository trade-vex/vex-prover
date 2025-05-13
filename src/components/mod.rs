use std::{marker::PhantomData, vec};

use addition::{AddComponent, AddElements, AddEval};
use order_match::{
    BuyAggressiveMatchComponent, BuyPassiveMatchComponent, MatchElements, MatchEval,
    SellAggressiveMatchComponent, SellPassiveMatchComponent,
};
use partial_order_match::{
    BuyAggressivePartialMatchComponent, BuyPassivePartialMatchComponent, PartialMatchEval,
    SellAggressivePartialMatchComponent, SellPassivePartialMatchComponent,
};
use stwo_prover::{
    constraint_framework::TraceLocationAllocator,
    core::{
        air::{Component, ComponentProver},
        backend::simd::SimdBackend,
        channel::Channel,
        fields::qm31::SecureField,
        pcs::TreeVec,
    },
};

use crate::{
    executor::{instruction::InstructionElements, state::StateElements},
    imt::side::{Aggressive, Buy, Passive, Sell},
    VexClaim, VexInteractionClaim,
};

use bytes::{AndElements, BytesComponent, LessThanU8Elements, RangeCheckU8Elements};
use insertions::{BuyInsertionComponent, InsertionsEval, SellInsertionComponent};
use less_than::{
    LessThanComponent, LessThanElements, StrictLessThanComponent, StrictLessThanElements,
};
use poseidon::{PoseidonComponent, PoseidonElements};
use processor::{ProcessorComponent, ProcessorEval};
pub mod addition;
pub mod bytes;
pub(crate) mod constraints_utils;
pub mod deletion;
pub mod insertions;
pub mod less_than;
pub mod order_match;
pub mod partial_order_match;
pub mod poseidon;

pub mod processor;
pub(crate) mod trace_utils;
pub use trace_utils::is_first;

/// Const trait that defines the number of columns in the trace table
pub trait TraceSize {
    /// Number of columns in preprocessed trace table
    const PREPROCESSED_COLS: usize;
    /// Number of columns in the main trace table
    const MAIN_COLS: usize;
    /// Number of columns in the interaction trace table
    const INTERACTION_COLS: usize;

    // Compile-time validation
    const ASSERT: () = assert!(Self::MAIN_COLS > 0 && Self::INTERACTION_COLS > 0);
}

/// Generic Claim to implement for claims each component
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Claim<T: TraceSize> {
    pub log_size: u32,
    _marker: PhantomData<T>,
}

impl<T: TraceSize> Claim<T> {
    pub const fn new(log_size: u32) -> Self {
        T::ASSERT;

        Self {
            log_size,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub const fn main_cols() -> usize {
        T::MAIN_COLS
    }

    #[inline(always)]
    pub const fn interaction_cols() -> usize {
        T::INTERACTION_COLS
    }

    #[inline]
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        TreeVec::new(vec![
            vec![self.log_size; T::PREPROCESSED_COLS],
            vec![self.log_size; T::MAIN_COLS],
            vec![self.log_size; T::INTERACTION_COLS],
        ])
    }

    #[inline(always)]
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(u64::from(self.log_size));
    }
}

/// Generic InteractionClaim to implement for interaction claims each component

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct InteractionClaim<T: TraceSize> {
    pub claimed_sum: SecureField,
    _marker: PhantomData<T>,
}

impl<T: TraceSize> InteractionClaim<T> {
    pub const fn new(claimed_sum: SecureField) -> Self {
        T::ASSERT;

        Self {
            claimed_sum,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

/// Interaction Elements for all the components of the system.
/// Interaction elements are used to combine values that are "used" or "yielded" by the components.
pub struct VexInteractionElements {
    pub instruction_elements: InstructionElements,
    pub state_elements: StateElements,
    pub poseidon_elements: PoseidonElements,
    pub less_than_elements: LessThanElements,
    pub strict_less_than_elements: StrictLessThanElements,
    pub less_than_u8_elements: LessThanU8Elements,
    pub and_elements: AndElements,
    pub range_check_u8_elements: RangeCheckU8Elements,
    pub match_elements: MatchElements,
    pub add_elements: AddElements,
}

impl VexInteractionElements {
    /// Draw all the interaction elements for the components.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            instruction_elements: InstructionElements::draw(channel),
            state_elements: StateElements::draw(channel),
            poseidon_elements: PoseidonElements::draw(channel),
            less_than_elements: LessThanElements::draw(channel),
            strict_less_than_elements: StrictLessThanElements::draw(channel),
            less_than_u8_elements: LessThanU8Elements::draw(channel),
            and_elements: AndElements::draw(channel),
            range_check_u8_elements: RangeCheckU8Elements::draw(channel),
            match_elements: MatchElements::draw(channel),
            add_elements: AddElements::draw(channel),
        }
    }
}

/// VexComponents is the main struct that holds all the components of the system.
pub struct VexComponents {
    processor: ProcessorComponent,
    buy_insert: BuyInsertionComponent,
    sell_insert: SellInsertionComponent,
    poseidon: PoseidonComponent,
    strict_less_than: StrictLessThanComponent,
    less_than: LessThanComponent,
    add_component: AddComponent,
    bytes: BytesComponent,
    buy_aggressive_match: BuyAggressiveMatchComponent,
    sell_aggressive_match: SellAggressiveMatchComponent,
    buy_passive_match: BuyPassiveMatchComponent,
    sell_passive_match: SellPassiveMatchComponent,
    buy_aggressive_partial_match: BuyAggressivePartialMatchComponent,
    sell_aggressive_partial_match: SellAggressivePartialMatchComponent,
    buy_passive_partial_match: BuyPassivePartialMatchComponent,
    sell_passive_partial_match: SellPassivePartialMatchComponent,
}

impl VexComponents {
    /// Create a new instance of VexComponents.
    pub fn new(
        claim: &VexClaim,
        interaction_elements: &VexInteractionElements,
        interaction_claim: &VexInteractionClaim,
    ) -> Self {
        let tree_span_provider = &mut TraceLocationAllocator::default();

        let bytes = bytes::BytesComponent::new(
            tree_span_provider,
            bytes::BytesEval {
                claim: claim.bytes_claim.clone(),
                and_elements: interaction_elements.and_elements.clone(),
                less_than_u8_elements: interaction_elements.less_than_u8_elements.clone(),
                range_check_u8_elements: interaction_elements.range_check_u8_elements.clone(),
            },
            interaction_claim.bytes_interaction_claim.claimed_sum,
        );

        let poseidon = poseidon::PoseidonComponent::new(
            tree_span_provider,
            poseidon::PoseidonEval {
                claim: claim.poseidon_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
            },
            interaction_claim.poseidon_interaction_claim.claimed_sum,
        );

        let strict_less_than = less_than::StrictLessThanComponent::new(
            tree_span_provider,
            less_than::LessThanEval {
                claim: claim.strict_less_than_claim.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                strict_less_than_elements: interaction_elements.strict_less_than_elements.clone(),
                less_than_u8_elements: interaction_elements.less_than_u8_elements.clone(),
            },
            interaction_claim
                .strict_less_than_interaction_claim
                .claimed_sum,
        );

        let less_than = LessThanComponent::new(
            tree_span_provider,
            less_than::LessThanEval {
                claim: claim.less_than_claim.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                strict_less_than_elements: interaction_elements.strict_less_than_elements.clone(),
                less_than_u8_elements: interaction_elements.less_than_u8_elements.clone(),
            },
            interaction_claim.less_than_interaction_claim.claimed_sum,
        );

        let add_component = AddComponent::new(
            tree_span_provider,
            AddEval {
                claim: claim.add_claim.clone(),
                range_check_u8_elements: interaction_elements.range_check_u8_elements.clone(),
                add_elements: interaction_elements.add_elements.clone(),
            },
            interaction_claim.add_interaction_claim.claimed_sum,
        );

        let processor = ProcessorComponent::new(
            tree_span_provider,
            ProcessorEval {
                claim: claim.processor_claim.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                state_elements: interaction_elements.state_elements.clone(),
            },
            interaction_claim.processor_interaction_claim.claimed_sum,
        );

        let buy_insert = BuyInsertionComponent::new(
            tree_span_provider,
            InsertionsEval {
                claim: claim.buy_insert_claim.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                strict_less_than_elements: interaction_elements.strict_less_than_elements.clone(),
                _side: PhantomData::<Buy>,
            },
            interaction_claim.buy_insert_interaction_claim.claimed_sum,
        );

        let sell_insert = SellInsertionComponent::new(
            tree_span_provider,
            InsertionsEval {
                claim: claim.sell_insert_claim.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                strict_less_than_elements: interaction_elements.strict_less_than_elements.clone(),
                _side: PhantomData::<Sell>,
            },
            interaction_claim.sell_insert_interaction_claim.claimed_sum,
        );

        let buy_aggressive_match = BuyAggressiveMatchComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.buy_aggressive_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Aggressive>,
            },
            interaction_claim
                .buy_aggressive_match_interaction_claim
                .claimed_sum,
        );

        let sell_aggressive_match = SellAggressiveMatchComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.sell_aggressive_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Aggressive>,
            },
            interaction_claim
                .sell_aggressive_match_interaction_claim
                .claimed_sum,
        );

        let buy_passive_match = BuyPassiveMatchComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.buy_passive_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Passive>,
            },
            interaction_claim
                .buy_passive_match_interaction_claim
                .claimed_sum,
        );

        let sell_passive_match = SellPassiveMatchComponent::new(
            tree_span_provider,
            MatchEval {
                claim: claim.sell_passive_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Passive>,
            },
            interaction_claim
                .sell_passive_match_interaction_claim
                .claimed_sum,
        );

        let buy_aggressive_partial_match = BuyAggressivePartialMatchComponent::new(
            tree_span_provider,
            PartialMatchEval {
                claim: claim.buy_aggressive_partial_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                add_elements: interaction_elements.add_elements.clone(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Aggressive>,
            },
            interaction_claim
                .buy_aggressive_partial_match_interaction_claim
                .claimed_sum,
        );

        let sell_aggressive_partial_match = SellAggressivePartialMatchComponent::new(
            tree_span_provider,
            PartialMatchEval {
                claim: claim.sell_aggressive_partial_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                add_elements: interaction_elements.add_elements.clone(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Aggressive>,
            },
            interaction_claim
                .sell_aggressive_partial_match_interaction_claim
                .claimed_sum,
        );

        let buy_passive_partial_match = BuyPassivePartialMatchComponent::new(
            tree_span_provider,
            PartialMatchEval {
                claim: claim.buy_passive_partial_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                add_elements: interaction_elements.add_elements.clone(),
                _side: PhantomData::<Buy>,
                _type: PhantomData::<Passive>,
            },
            interaction_claim
                .buy_passive_partial_match_interaction_claim
                .claimed_sum,
        );

        let sell_passive_partial_match = SellPassivePartialMatchComponent::new(
            tree_span_provider,
            PartialMatchEval {
                claim: claim.sell_passive_partial_match_claim.clone(),
                poseidon_elements: interaction_elements.poseidon_elements.clone(),
                less_than_elements: interaction_elements.less_than_elements.clone(),
                match_elements: interaction_elements.match_elements.clone(),
                instruction_elements: interaction_elements.instruction_elements.clone(),
                add_elements: interaction_elements.add_elements.clone(),
                _side: PhantomData::<Sell>,
                _type: PhantomData::<Passive>,
            },
            interaction_claim
                .sell_passive_partial_match_interaction_claim
                .claimed_sum,
        );

        Self {
            processor,
            strict_less_than,
            less_than,
            add_component,
            buy_insert,
            sell_insert,
            poseidon,
            bytes,
            buy_aggressive_match,
            sell_aggressive_match,
            buy_passive_match,
            sell_passive_match,
            buy_aggressive_partial_match,
            sell_aggressive_partial_match,
            buy_passive_partial_match,
            sell_passive_partial_match,
        }
    }

    /// Returns the ComponentProver of each components whose log sizes are in decreasing order.
    pub fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        vec![
            &self.bytes,
            &self.poseidon,
            &self.strict_less_than,
            &self.less_than,
            &self.add_component,
            &self.processor,
            &self.buy_insert,
            &self.sell_insert,
            &self.buy_aggressive_match,
            &self.sell_aggressive_match,
            &self.buy_passive_match,
            &self.sell_passive_match,
            &self.buy_aggressive_partial_match,
            &self.sell_aggressive_partial_match,
            &self.buy_passive_partial_match,
            &self.sell_passive_partial_match,
        ]
    }

    /// Returns the Component of each components whose log sizes are in decreasing order.
    pub fn components(&self) -> Vec<&dyn Component> {
        self.provers()
            .into_iter()
            .map(|component| component as &dyn Component)
            .collect()
    }
}

/// The Components contained in VEX
#[derive(Clone, Copy)]
pub enum VexComponent {
    /// Hiher Level Tree Components
    InsertBuyOrder,
    InsertSellOrder,
    UpdateBuyOrder,
    UpdateSellOrder,
    CancelBuyOrder,
    CancelSellOrder,
    MatchAggressiveBuy,
    MatchPassiveBuy,
    MatchAggressiveSell,
    MatchPassiveSell,
    PartialMatchAggressiveBuy,
    PartialMatchPassiveBuy,
    PartialMatchAggressiveSell,
    PartialMatchPassiveSell,

    /// Sub Operations Components
    LessThan,
    Bytes,
    StrictLessThan,
    Addition,
    Poseidon,

    /// Main Processor Component
    Processor,
}

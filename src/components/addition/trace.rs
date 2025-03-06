use crate::{
    components::{bytes::AndElements, Claim, InteractionClaim, TraceSize},
    types::N_U64_LIMBS,
};
use itertools::{chain, Itertools};
use num_traits::{Zero, One};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use std::array;
use stwo_air_utils::trace::component_trace::ComponentTrace;
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, preprocessed_columns::IsFirst, Relation},
    core::{
        backend::simd::{
            m31::{PackedBaseField, LOG_N_LANES, N_LANES},
            qm31::PackedSecureField,
            SimdBackend,
        },
        fields::m31::BaseField,
        poly::{circle::CircleEvaluation, BitReversedOrder},
        ColumnVec,
    },
};
use tracing::{debug, span, Level};
use crate::components::bytes::RangeCheckU8Elements;
use super::{AddColumn, AddElements, AddOperations};

pub fn preprocessed_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    vec![IsFirst::new(log_size).gen_column_simd()]
}

/// Trace for the Less Than Operations, each row consisting of a LessThanOp
pub fn trace(
    mut add_operations: AddOperations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    Claim<AddColumn>,
) {
    let _span = span!(Level::INFO, "Add: Main Trace").entered();
    // Calculate the log size, ensuring the trace size is a power of 2
    let log_size = (add_operations.len() - 1).ilog2() + 1;
    debug!("Log Size: {}", log_size);
    // Pad operations to ensure a power of 2 trace size
    for _ in 0..(1 << log_size) - add_operations.len() {
        add_operations.push([BaseField::zero(); AddColumn::MAIN_COLS]);
    }
    let mut trace = ComponentTrace::<{ AddColumn::MAIN_COLS }>::zeroed(log_size);
    // Each row of the trace is a AddOp field elements arranged as per the `AddColumn`
    trace
        .par_iter_mut()
        .zip(
            add_operations
                .into_par_iter()
                .chunks(N_LANES)  // Process in chunks of N_LANES (SIMD width)
                .into_par_iter(),
        )
        .for_each(|(row, data)| {
            for (i, cell) in row.into_iter().enumerate() {
                let column_chunk = core::array::from_fn(|j| data[j][i]);
                *cell = PackedBaseField::from_array(column_chunk);
            }
        });
    // Convert trace to evaluations and create a claim
    (trace.to_evals().to_vec(), Claim::new(log_size))
}

// Interaction Trace, "use" the AddU8Elements for byte addition checks
// and "yield" the AddElements for the actual addition results
pub fn interaction_trace(
    trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    range_check_u8_elements: &RangeCheckU8Elements,
    add_elements: &AddElements,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    InteractionClaim<AddColumn>,
) {
    let _span = span!(Level::INFO, "Add: Interaction Trace").entered();
    let log_size = trace[0].domain.log_size();
    let mut logup_gen = LogupTraceGenerator::new(log_size);

    // Extract the columns from the trace used for the interaction trace
    let a_col: [&Vec<PackedBaseField>; N_U64_LIMBS] =
        array::from_fn(|i| &trace[AddColumn::A + i].data);
    let b_col: [&Vec<PackedBaseField>; N_U64_LIMBS] =
        array::from_fn(|i| &trace[AddColumn::B + i].data);
    let c_col: [&Vec<PackedBaseField>; N_U64_LIMBS] =
        array::from_fn(|i| &trace[AddColumn::C + i].data);
    let carry_col: [&Vec<PackedBaseField>; N_U64_LIMBS - 1] =
        array::from_fn(|i| &trace[AddColumn::CARRY + i].data);
    let is_real_col = &trace[AddColumn::IS_REAL].data;

    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let a: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| a_col[i][vec_row]);
        let b: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| b_col[i][vec_row]);
        let c: [PackedBaseField; N_U64_LIMBS] = array::from_fn(|i| c_col[i][vec_row]);
        let carry: [PackedBaseField; N_U64_LIMBS - 1] = array::from_fn(|i| carry_col[i][vec_row]);

        // // AddU8Elements Values, LookUp ensures byte-wise addition correctness 
        let range_check_u8_values: Vec<Vec<PackedBaseField>> = (0..N_U64_LIMBS)
            .map(|i| vec![a[i], b[i]])
            .collect();
        // Combine U8 Element checks
        // let range_check_u8_values = chain!(a.into_iter(), b.into_iter()).collect_vec();
        // let p_u8: PackedSecureField = range_check_u8_elements.combine(&range_check_u8_values);
                // Initialize a combined product to accumulate all relation entries
        // let mut combined_u8_check = PackedSecureField::one();

        // // Process range checks for each a[i] and b[i] pair, matching the constraint logic
        // for i in 0..N_U64_LIMBS {
        //     let range_check_pair = vec![a[i], b[i]];
        //     let pair_check = range_check_u8_elements.combine(&range_check_pair);
        //     combined_u8_check = combined_u8_check * pair_check;
        // }
        // let range_check_u8_values: Vec<PackedBaseField> = chain!(a.into_iter(), b.into_iter()).collect_vec();
        let p_u8: PackedSecureField = range_check_u8_elements.combine(&range_check_u8_values.concat());
        
        // // Byte-wise addition and carry constraints
        // let mut add_constraint_values = Vec::new();
        // let mut range_check_values = Vec::new();

        // // Process each byte limb
        // for i in 0..N_U64_LIMBS {
        //     // Range check for a, b, c
        //     range_check_values.extend([a[i], b[i], c[i]]);

        //     // Manual byte-wise addition constraint
        //     if i == 0 {
        //         // First byte: no incoming carry
        //         let first_byte_sum = a[i] + b[i];
        //         let first_byte_constraint = first_byte_sum - c[i];
        //         let first_carry = if first_byte_sum >= BaseField::from(256u32) { 
        //             BaseField::one() 
        //         } else { 
        //             BaseField::zero() 
        //         };
        //         add_constraint_values.extend([a[i], b[i], c[i], first_carry]);
        //         // Verify first carry matches the trace
        //         assert_eq!(first_carry, carry[i]);
        //     } else {
        //         // Subsequent bytes: with incoming carry
        //         let byte_sum = a[i] + b[i] + carry[i-1];
        //         let byte_constraint = byte_sum - c[i];
        //         let next_carry = if byte_sum >= BaseField::from(256u32) { 
        //             BaseField::one() 
        //         } else { 
        //             BaseField::zero() 
        //         };
        //         add_constraint_values.extend([a[i], b[i], c[i], next_carry]);
                
        //         // For all but the last byte, verify carry
        //         if i < N_U64_LIMBS - 1 {
        //             assert_eq!(next_carry, carry[i]);
        //         }
        //     }
        // }

        // Range Check using RangeCheckU8Elements
        // let p_range_check: PackedSecureField = range_check_u8_elements.combine(&range_check_u8_values);


        // AddElements Values, includes all a, b, c limbs
        let add_values: Vec<PackedBaseField> = chain!(a.into_iter(), b.into_iter(), c.into_iter(), carry.into_iter()).collect_vec();
        let p_elements: PackedSecureField = add_elements.combine(&add_values);
        // 1/p_u8 - 1/p_elements is the claimed sum for the row
        col_gen.write_frac(vec_row, (p_elements - p_u8) * is_real_col[vec_row], p_u8 * p_elements);
    }
    col_gen.finalize_col();
    //     // AddElements including a, b, c limbs and carries
    // let add_values: Vec<PackedBaseField> = chain!(
    //     a.into_iter(), 
    //     b.into_iter(), 
    //     c.into_iter(), 
    //     carry.into_iter()
    // ).collect_vec();
    // let p_add_elements: PackedSecureField = add_elements.combine(&add_values);

    // // Write fractional entry, filtering with is_real flag
    // col_gen.write_frac(
    //     vec_row, 
    //     (p_add_elements - p_range_check) * is_real_col[vec_row], 
    //     p_range_check * p_add_elements
    // );
    // }
    // col_gen.finalize_col();
    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, InteractionClaim::new(claimed_sum))
}
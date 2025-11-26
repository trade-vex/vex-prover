use num_traits::One;
use std::array;

use itertools::chain;
use stwo_prover::constraint_framework::{EvalAtRow, RelationEntry};

use crate::{
    hash::{N_HASH, N_STATE},
    imt::{IndexBits, LeafFelts, MerklePath, MerkleProof},
};

use super::poseidon::PoseidonElements;

pub fn eval_merkle_proof<E: EvalAtRow>(
    eval: &mut E,
    proof: &MerkleProof<E::F>,
    path: &MerklePath<E::F>,
    leaf: &LeafFelts<E::F>,
    index_bits: &IndexBits<E::F>,
    poseidon_elements: &PoseidonElements,
    mult: E::EF,
) {
    // evaluate leaf hash
    let leaf_vec: Vec<E::F> = leaf[0..N_STATE].into();
    eval.add_to_relation(RelationEntry::new(
        poseidon_elements,
        mult.clone(),
        &chain!(leaf_vec.iter().cloned(), path[0].clone().into_iter()).collect::<Vec<_>>(),
    ));

    let mut curr = path[0].clone();
    for (i, (sibling, hash)) in proof.iter().zip(path.iter().skip(1)).enumerate() {
        let index_bit = index_bits[i].clone();
        let first: [E::F; N_HASH] = array::from_fn(|j| {
            index_bit.clone() * sibling[j].clone()
                + (E::F::one() - index_bit.clone()) * curr[j].clone()
        });
        let second: [E::F; N_HASH] = array::from_fn(|j| {
            index_bit.clone() * curr[j].clone()
                + (E::F::one() - index_bit.clone()) * sibling[j].clone()
        });
        let values: Vec<E::F> = chain!(
            first.into_iter(),
            second.into_iter(),
            hash.clone().into_iter()
        )
        .collect();
        eval.add_to_relation(RelationEntry::new(poseidon_elements, mult.clone(), &values));
        curr = hash.clone();
    }
}

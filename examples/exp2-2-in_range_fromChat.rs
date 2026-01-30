//use bulletproofs::r1cs::{ProverCS, VerifierCS, ConstraintSystem, R1CSError, Variable};
//use bulletproofs::r1cs::LinearCombination;
//use bulletproofs::r1cs::R1CSProof;
//use bulletproofs::r1cs::Verifier;
//use bulletproofs::r1cs::Prover;
//use bulletproofs::r1cs::AllocatedQuantity;
//use bulletproofs::BulletproofGens;
//use bulletproofs::PedersenGens;
//use curve25519_dalek::scalar::Scalar;

extern crate rand;
 use rand::thread_rng;

 extern crate curve25519_dalek;
 use curve25519_dalek::scalar::Scalar;

 extern crate merlin;
 use merlin::Transcript;

 extern crate bulletproofs;
 use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};

//mod gadget_zero_nonzero;
//mod utils;
extern crate gadget_zero_nonzero;
use crate::gadget_zero_nonzero::bound_check_gadget;
extern crate utils;
use crate::utils::positive_no_gadget;

fn main() {
    // Setup
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);
    let mut transcript = Transcript::new(b"Example");

    // Input values
    let quantity_v = 15u64;
    let max = 30u64;
    let min = 10u64;
    let a_val = quantity_v - min;
    let b_val = max - quantity_v;

    // Prover
    let mut rng = rand::thread_rng();
    let (commit_v, v_blinding) = pc_gens.commit(Scalar::from(quantity_v), Scalar::random(&mut rng));
    let (commit_a, a_blinding) = pc_gens.commit(Scalar::from(a_val), Scalar::random(&mut rng));
    let (commit_b, b_blinding) = pc_gens.commit(Scalar::from(b_val), Scalar::random(&mut rng));

    let mut prover_transcript = Transcript::new(b"BoundCheck");
    let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

    // Allocate inputs
    let v = prover.commit(Scalar::from(quantity_v), v_blinding);
    let a = prover.commit(Scalar::from(a_val), a_blinding);
    let b = prover.commit(Scalar::from(b_val), b_blinding);

    let v_alloc = AllocatedQuantity {
        variable: v,
        assignment: Some(Scalar::from(quantity_v)),
    };
    let a_alloc = AllocatedQuantity {
        variable: a,
        assignment: Some(Scalar::from(a_val)),
    };
    let b_alloc = AllocatedQuantity {
        variable: b,
        assignment: Some(Scalar::from(b_val)),
    };

    // Call gadget
    let n = 6;
    bound_check_gadget(&mut prover, v_alloc, a_alloc, b_alloc, max, min, n).unwrap();

    // Create proof
    let proof = prover.prove(&bp_gens).unwrap();

    // Verifier
    let mut verifier_transcript = Transcript::new(b"BoundCheck");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let v_var = verifier.commit(commit_v.compress());
    let a_var = verifier.commit(commit_a.compress());
    let b_var = verifier.commit(commit_b.compress());

    let v_alloc = AllocatedQuantity {
        variable: v_var,
        assignment: None,
    };
    let a_alloc = AllocatedQuantity {
        variable: a_var,
        assignment: None,
    };
    let b_alloc = AllocatedQuantity {
        variable: b_var,
        assignment: None,
    };

    bound_check_gadget(&mut verifier, v_alloc, a_alloc, b_alloc, max, min, n).unwrap();

    assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
}


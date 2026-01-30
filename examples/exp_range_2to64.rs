extern crate curve25519_dalek;
extern crate bulletproofs;
extern crate merlin;

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

fn main() {
    // Generators
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(64, 1);

    // Secret value
    let value: u64 = 42;
    let blinding = Scalar::random(&mut rand::thread_rng());

    // Prover's scope
    let mut prover_transcript = Transcript::new(b"RangeProofExample");
    let (proof, committed_value) = RangeProof::prove_single(
        &bp_gens,
        &pc_gens,
        &mut prover_transcript,
        value,
        &blinding,
        64,
    ).expect("proof generation should not fail");

    // Verifier's scope
    let mut verifier_transcript = Transcript::new(b"RangeProofExample");
    assert!(
        proof.verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 64).is_ok()
    );
    println!("Range proof verified!");
}


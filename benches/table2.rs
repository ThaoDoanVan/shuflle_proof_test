// Table 2: Verifier Performance 
//
// Run with: cargo bench --bench table2 --features yoloproofs
//
// This reproduces Table 2 from the paper

extern crate bulletproofs;
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Variable, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs::r1cs::LinearCombination;

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

extern crate merlin;
use merlin::Transcript;

extern crate rand;
use rand::Rng;
use rand::seq::SliceRandom;

extern crate bincode;

// ============================================================================
// KShuffleGadget (same as quick.rs and table1.rs)
// ============================================================================

struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: &[Variable], y: &[Scalar], k_original: usize) {
        let _one = Scalar::one();
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len();
        assert_eq!(x.len(), y.len());

        let mut prod_y = Scalar::one();
        for yi in y {
            prod_y *= *yi - z;
        }

        let mut prev_lc = if 0 >= k_original {
            cs.constrain(x[0] - Scalar::zero());
            LinearCombination::from(-z)
        } else {
            x[0] - z
        };

        for i in 1..k {
            if i >= k_original {
                cs.constrain(x[i] - Scalar::zero());
                prev_lc = prev_lc * (-z);
            } else {
                let term = x[i] - z;
                let (_, _, out_var) = cs.multiply(prev_lc, term);
                prev_lc = LinearCombination::from(out_var);
            }
        }

        cs.constrain(prev_lc - prod_y);
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
        C1_prime: &[RistrettoPoint],
        C2_prime: &[RistrettoPoint],
        r_prime: Scalar,
        k_fold: usize,
        num_rounds: usize,
    ) -> Result<(R1CSProof, CompressedRistretto), R1CSError> {
        let k = input.len();
        let k_original = C1_prime.len();
        if k <= 1 { return Err(R1CSError::InputLengthError); }
        
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());

        let mut prover = Prover::new(&bp_gens, &pc_gens, transcript);
        let mut blinding_rng = rand::thread_rng();
        let v_blinding = Scalar::random(&mut blinding_rng);
        let (output_commitment, output_vars) = prover.commit_vec(&output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, &input, k_original);
        let proof = cs.prove(C1_prime, C2_prime, r_prime, k_fold, num_rounds)?;
        Ok((proof, output_commitment))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        proof: &R1CSProof,
        input: &[Scalar],
        output_commitment: CompressedRistretto,
        C1_prime: &[RistrettoPoint],
        C2_prime: &[RistrettoPoint],
        C: &[RistrettoPoint],
    ) -> Result<(), R1CSError> {
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());

        let mut verifier = Verifier::new(&bp_gens, &pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        let k_original = C1_prime.len();

        Self::fill_cs(&mut cs, &output_vars, &input, k_original);
        cs.verify(proof, C1_prime, C2_prime, C)
    }
}

fn kshuffle_verify_helper(num_rounds: usize, k: usize, k_original: usize, k_fold: usize, c: &mut Criterion) {
    let label = format!("table2/verifier/n={}/k={}/d={}", k_original, k_fold, num_rounds);

    c.bench_function(&label, move |b| {
        let mut rng = rand::thread_rng();
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k_original)
            .map(|_| Scalar::from(rng.gen_range(min, max)))
            .collect();

        let mut indices: Vec<usize> = (0..k_original).collect();
        indices.shuffle(&mut rng);
        let output: Vec<Scalar> = indices.iter().map(|&i| input[i]).collect();

        let C1: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let C2: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(k, 1);
        let g = pc_gens.B;
        let h = pc_gens.B_blinding; 

        let mut C1_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C1[i]).collect();
        let mut C2_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C2[i]).collect();
        let mut r_prime = Scalar::zero();

        for (j, &i) in indices.iter().enumerate() {
            let r_i = Scalar::random(&mut rng);
            C1_prime[j] = C1[i] + g * r_i;
            C2_prime[j] = C2[i] + h * r_i;
            r_prime += r_i * input[i]; 
        }
        r_prime = -r_prime;

        let mut input_padded = input.clone();
        let mut output_padded = output.clone();
        input_padded.resize(k, Scalar::zero());
        output_padded.resize(k, Scalar::zero());

        // Create proof ONCE (outside benchmark)
        let mut prover_transcript = Transcript::new(b"ShuffleTest");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens, &bp_gens, &mut prover_transcript, 
            &input_padded, &output_padded,
            &C1_prime, &C2_prime, r_prime, k_fold, num_rounds,
        ).expect("Proving failed");
        
        let mut C: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); 2];
        for i in 0..k_original {
            C[0] = C[0] + C1[i] * input[i];
            C[1] = C[1] + C2[i] * input[i];
        }

        let serialized_proof = bincode::serialize(&proof).unwrap();
      
        // BENCHMARK: Deserialization + Verification
        b.iter(|| {
            let deserialized_proof: R1CSProof = bincode::deserialize(&serialized_proof).unwrap();
            let mut verifier_transcript = Transcript::new(b"ShuffleTest");
            let result = KShuffleGadget::verify(
                &pc_gens, &bp_gens, &mut verifier_transcript,
                &deserialized_proof, &input_padded, out_commitment,
                &C1_prime, &C2_prime, &C,
            );
            assert!(result.is_ok());
        })
    });
}

// ============================================================================
// Table 2: Verifier Performance
// ============================================================================

fn table2_verifier_performance(c: &mut Criterion) {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║     TABLE 2: Verifier Performance (5 samples)                ║");
    println!("║  Reproduces Table 2 from paper                               ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\nThis benchmarks verifier efficiency.");
    println!();
    println!("  For custom parameters:");
    println!("    Edit benches/r1cs.rs (lines 28-43)");
    println!("    cargo bench --bench r1cs --features yoloproofs");
    println!("================================================================\n");


    // From paper Table 2 (only k=4, the optimal configuration)
    let test_cases = vec![
        // (n, k, d)
        (1024,  4, 5),
        (4096,  4, 6),
        (16384, 4, 7),
        (65536, 4, 8),
    ];

    for (i, (n, k, d)) in test_cases.iter().enumerate() {
        println!("[{}/{}] n={:6}, k={}, d={}", 
                 i+1, test_cases.len(), n, k, d);
        kshuffle_verify_helper(*d, *n, *n, *k, c);
    }

    println!("\n Table 2 complete!");
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(5)
        .measurement_time(std::time::Duration::from_secs(20));
    targets = table2_verifier_performance
}

criterion_main!(benches);

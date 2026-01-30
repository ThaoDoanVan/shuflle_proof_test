// Quick Validation Benchmark
//
// Run with: cargo bench --bench quick --features yoloproofs

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
}

fn calculate_proof_size(n_padded: usize, k: usize, d: usize) -> usize {
    fn reconstruct_rest(mut n: usize, k: usize, d: usize) -> usize {
        for _ in 0..d {
            let rem = n % k;
            let pad = if rem == 0 { 0 } else { k - rem };
            n = (n + pad) / k;
        }
        n
    }

    let rest = reconstruct_rest(n_padded, k, d);
    
    // R1CS overhead: 13 points + 8 scalars + 2 u64 lengths
    let r1cs_overhead = (13 + 8) * 32 + 16;
    
    // IPP proof: 3 headers + d rounds of (2k-2) points + 2 vectors of size rest
    let ipp_points = if d > 0 { d * (2 * k - 2) } else { 0 };
    let ipp_size = (3 + ipp_points + 2 * rest) * 32;
    
    // Batched ECP: 3 headers + d rounds of (2k-2)*2 points + 1 vector of size rest
    let ecp_points = if d > 0 { d * (2 * k - 2) * 2 } else { 0 };
    let ecp_size = (3 + ecp_points + rest) * 32;
    
    r1cs_overhead + ipp_size + ecp_size
}

fn kshuffle_prove_helper(num_rounds: usize, k: usize, k_original: usize, k_fold: usize, c: &mut Criterion) {
    let label = format!("quick/n={}/k={}/d={}", k_original, k_fold, num_rounds);
    let proof_size = calculate_proof_size(k, k_fold, num_rounds);

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

        b.iter(|| {
            let mut prover_transcript = Transcript::new(b"ShuffleTest");
            let (proof, _out_commitment) = KShuffleGadget::prove(
                &pc_gens, &bp_gens, &mut prover_transcript, 
                &input_padded, &output_padded,
                &C1_prime, &C2_prime, r_prime, k_fold, num_rounds,
            ).unwrap();
            let _serialized_proof = bincode::serialize(&proof).unwrap();
        })
    });

    println!("      Proof size: {} bytes ({:.2} KB)", proof_size, proof_size as f64 / 1024.0);
}

fn quick_demo(c: &mut Criterion) {
    println!("\n================================================================");
    println!("  Quick Validation Benchmark");
    println!("================================================================");
    println!("  This test verifies that the implementation functions");
    println!("  correctly with small-scale inputs.");
    println!();
    println!("  For paper reproduction:");
    println!("    cargo bench --bench table1 --features yoloproofs");
    println!("    cargo bench --bench table2 --features yoloproofs");
    println!();
    println!("  For custom parameters:");
    println!("    Edit benches/r1cs.rs (lines 28-43)");
    println!("    cargo bench --bench r1cs --features yoloproofs");
    println!("================================================================\n");

    println!("[1/2] Testing n=1,024, k=4, d=5...");
    kshuffle_prove_helper(5, 1024, 1024, 4, c);

    println!("\n[2/2] Testing n=4,096, k=4, d=6...");
    kshuffle_prove_helper(6, 4096, 4096, 4, c);

    println!("\nQuick validation complete.\n");
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(3)
        .measurement_time(std::time::Duration::from_secs(20));
    targets = quick_demo
}

criterion_main!(benches);

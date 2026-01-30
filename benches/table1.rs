// Table 1: Prover Performance 
//
// Run with: cargo bench --bench table1 --features yoloproofs
//
// This reproduces Table 1 from the paper, comparing Binary (k=2) vs 4-ary (k=4)


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
// KShuffleGadget 
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
}

fn kshuffle_prove_helper(num_rounds: usize, k: usize, k_original: usize, k_fold: usize, c: &mut Criterion) {
    let label = format!("table1/prover/n={}/k={}/d={}", k_original, k_fold, num_rounds);

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
}

// ============================================================================
// Table 1: Prover Performance
// ============================================================================

fn table1_prover_performance(c: &mut Criterion) {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║      TABLE 1: Prover Performance (5 samples)                 ║");
    println!("║  Reproduces Table 1 from paper (Binary vs 4-ary)             ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\nThis benchmarks prover efficiency at different scales.");
    println!();
    println!("  For custom parameters:");
    println!("    Edit benches/r1cs.rs (lines 28-43)");
    println!("    cargo bench --bench r1cs --features yoloproofs");
    println!("================================================================\n");



    // From paper Table 1
    let test_cases = vec![
        // (n, k, d, label)
        (1024,    2, 10, "Binary"),
        (1024,    4, 5,  "4-ary"),
        (4096,    2, 12, "Binary"),
        (4096,    4, 6,  "4-ary"),
        (16384,   2, 14, "Binary"),
        (16384,   4, 7,  "4-ary"),
        (65536,   2, 16, "Binary"),
        (65536,   4, 8,  "4-ary"),
    ];

    for (i, (n, k, d, label)) in test_cases.iter().enumerate() {
        println!("[{}/{}] n={:6}, k={}, d={:2} ({})", 
                 i+1, test_cases.len(), n, k, d, label);
        kshuffle_prove_helper(*d, *n, *n, *k, c);
    }

    println!("\n Table 1 complete!");
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(5)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = table1_prover_performance
}

criterion_main!(benches);

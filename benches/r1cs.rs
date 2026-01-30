extern crate bulletproofs;
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Variable, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs::r1cs::LinearCombination;

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

extern crate merlin;
use merlin::Transcript;

extern crate rand;
use rand::Rng;

use curve25519_dalek::ristretto::RistrettoPoint;
use rand::seq::SliceRandom;

// Import bincode for serialization benchmarks
extern crate bincode;
use bincode::deserialize;

// For finding the best k, d, n_padded 
use std::ops::RangeInclusive;

/// Configuration result for the optimal proof strategy
#[derive(Debug, Clone)]
pub struct ProofConfig {
    pub k: usize,
    pub d: usize,
    pub m: usize,
    pub n_padded: usize,
    pub padding: usize,
    pub exact_proof_size_bytes: usize,
}

/// Finds the top 3 configurations (k, d, m) that minimize padding
/// while keeping the proof size under a specified limit.
/// 
/// Uses EXACT proof size calculation based on serialization logic.
pub fn find_optimal_pad_config(
    n_inputs: usize,
    allowed_k: &[usize],
    allowed_d_range: RangeInclusive<usize>,
    max_proof_bytes: usize,
) -> Vec<ProofConfig> { // CHANGED: Return Vec
    let mut valid_configs = Vec::new();

    println!("\n--- Searching for Optimal Configs (N={}, MaxBytes={}) ---", n_inputs, max_proof_bytes);

    for &k in allowed_k {
        // Iterate only through the user-specified range of d
        for d in allowed_d_range.clone() {
            
            // 1. Calculate Reduction Factor R = k^d
            // Handle potential overflow
            let r_opt = k.checked_pow(d as u32);
            if r_opt.is_none() { continue; } 
            let r = r_opt.unwrap();

            // 2. Calculate required 'm' (stop vector size)
            // m = ceil(N / R) -> (N + R - 1) / R
            let m = (n_inputs + r - 1) / r;

            // 3. Calculate n_padded
            let n_padded = m * r;
            let padding = n_padded - n_inputs;

            // 4. Calculate EXACT Proof Size
            // Formula derived from proof.rs and inner_product_proof.rs serialization:
            
            // A. Fixed R1CS Header
            // 13 Points (13 * 32) + 8 Scalars (8 * 32) + 2 u64 prefixes (2 * 8)
            // 416 + 256 + 16 = 688 bytes
            let fixed_header_size = 688;

            // B. IPP Proof Size
            // Header: k, d, m (padded to 32 bytes each) = 96 bytes
            // U_vecs: d rounds * (2k - 2) points * 32 bytes
            // Final vectors: (a_final + b_final) = 2 * m * 32 bytes
            let ipp_size = 96 
                         + d * (2 * k - 2) * 32 
                         + 2 * m * 32;

            // C. Batched ECP Size
            // Header: k, d, m (padded to 32 bytes each) = 96 bytes
            // A_vecs: d rounds * (2k - 2) tuples * 2 points/tuple * 32 bytes
            // Final witness: z = m * 32 bytes
            let ecp_size = 96 
                         + d * (2 * k - 2) * 2 * 32 
                         + m * 32;

            let total_size = fixed_header_size + ipp_size + ecp_size;

            // 5. Store Valid Configs
            if total_size <= max_proof_bytes {
                valid_configs.push(ProofConfig {
                    k,
                    d,
                    m,
                    n_padded,
                    padding,
                    exact_proof_size_bytes: total_size,
                });
            }
        }
    }

    if valid_configs.is_empty() {
        panic!("No configuration found fitting the proof size limit! Increase limit or allowed d range.");
    }

    // 6. Sort to find the best
    // Priority 1: Padding (Low is better)
    // Priority 2: Proof Size (Low is better)
    valid_configs.sort_by(|a, b| {
        match a.padding.cmp(&b.padding) {
            std::cmp::Ordering::Equal => a.exact_proof_size_bytes.cmp(&b.exact_proof_size_bytes),
            other => other,
        }
    });

    // Take top 3
    let top_configs: Vec<ProofConfig> = valid_configs.into_iter().take(3).collect();

    println!("Top {} Configs found:", top_configs.len());
    for (i, c) in top_configs.iter().enumerate() {
        println!("  #{}: k={}, d={}, m={} | Padding={} | Exact Size={} bytes", 
                 i+1, c.k, c.d, c.m, c.padding, c.exact_proof_size_bytes);
    }
    
    top_configs
}

pub fn find_optimal_pad_config1(
    n_inputs: usize,
    allowed_k: &[usize],
    allowed_d_range: RangeInclusive<usize>,
    max_proof_bytes: usize,
) -> Vec<ProofConfig> { // CHANGED: Return Vec
    let mut valid_configs = Vec::new();

    println!("\n--- Searching for Optimal Configs (N={}, MaxBytes={}) ---", n_inputs, max_proof_bytes);

    for &k in allowed_k {
        // Iterate only through the user-specified range of d
        for d in allowed_d_range.clone() {
            
            // 1. Calculate Reduction Factor R = k^d
            // Handle potential overflow
            let r_opt = k.checked_pow(d as u32);
            if r_opt.is_none() { continue; } 
            let r = r_opt.unwrap();

            // 2. Calculate required 'm' (stop vector size)
            // m = ceil(N / R) -> (N + R - 1) / R
            let m = (n_inputs + r - 1) / r;

            // 3. Calculate n_padded
            let n_padded = m * r;
            let padding = n_padded - n_inputs;

            // 4. Calculate EXACT Proof Size
            // Formula derived from proof.rs and inner_product_proof.rs serialization:
            
            // A. Fixed R1CS Header
            // 13 Points (13 * 32) + 8 Scalars (8 * 32) + 2 u64 prefixes (2 * 8)
            // 416 + 256 + 16 = 688 bytes
            let fixed_header_size = 688;

            // B. IPP Proof Size
            // Header: k, d, m (padded to 32 bytes each) = 96 bytes
            // U_vecs: d rounds * (2k - 2) points * 32 bytes
            // Final vectors: (a_final + b_final) = 2 * m * 32 bytes
            let ipp_size = 96 
                         + d * (2 * k - 2) * 32 
                         + 2 * m * 32;

            // C. Batched ECP Size
            // Header: k, d, m (padded to 32 bytes each) = 96 bytes
            // A_vecs: d rounds * (2k - 2) tuples * 2 points/tuple * 32 bytes
            // Final witness: z = m * 32 bytes
            let ecp_size = 96 
                         + d * (2 * k - 2) * 2 * 32 
                         + m * 32;

            let total_size = fixed_header_size + ipp_size + ecp_size;

            // 5. Store Valid Configs
            if total_size <= max_proof_bytes {
                valid_configs.push(ProofConfig {
                    k,
                    d,
                    m,
                    n_padded,
                    padding,
                    exact_proof_size_bytes: total_size,
                });
            }
        }
    }

    if valid_configs.is_empty() {
        panic!("No configuration found fitting the proof size limit! Increase limit or allowed d range.");
    }

    // 6. Sort to find the best
    // 1. k (Low is faster)
    // 2. Exact Size (Low is better for bandwidth)
    // 3. Padding (Tie-breaker)
    valid_configs.sort_by(|a, b| {
        match a.k.cmp(&b.k) {
            std::cmp::Ordering::Equal => {
                match a.exact_proof_size_bytes.cmp(&b.exact_proof_size_bytes) {
                    std::cmp::Ordering::Equal => a.padding.cmp(&b.padding),
                    other => other,
                }
            }
            other => other,
        }
    });

    // Take top 3
    let top_configs: Vec<ProofConfig> = valid_configs.into_iter().take(3).collect();

    println!("Top {} Configs found:", top_configs.len());
    for (i, c) in top_configs.iter().enumerate() {
        println!("  #{}: k={}, d={}, m={} | Padding={} | Exact Size={} bytes", 
                 i+1, c.k, c.d, c.m, c.padding, c.exact_proof_size_bytes);
    }
    
    top_configs
}

/// Finds optimal configurations prioritizing PROVER SPEED above all else.
/// 
/// Sorting Logic:
/// 1. k (Ascending): Lower k is significantly faster (k=2 >>> k=3).
/// 2. d (Ascending): Fewer rounds = Less computation (Shallow Folding).
/// 3. Padding (Ascending): Less waste.
pub fn find_optimal_pad_config2(
    n_inputs: usize,
    allowed_k: &[usize],
    allowed_d_range: RangeInclusive<usize>,
    max_proof_bytes: usize,
) -> Vec<ProofConfig> {
    let mut valid_configs = Vec::new();

    println!("\n--- Searching for Fastest Prover Configs (N={}, MaxBytes={}) ---", n_inputs, max_proof_bytes);

    for &k in allowed_k {
        for d in allowed_d_range.clone() {
            // 1. Calculate R and m
            let r_opt = k.checked_pow(d as u32);
            if r_opt.is_none() { continue; } 
            let r = r_opt.unwrap();
            let m = (n_inputs + r - 1) / r;

            // 2. Calculate n_padded
            let n_padded = m * r;
            let padding = n_padded - n_inputs;

            // 3. Calculate Exact Proof Size
            let fixed_header_size = 688;
            let ipp_size = 96 + d * (2 * k - 2) * 32 + 2 * m * 32;
            let ecp_size = 96 + d * (2 * k - 2) * 2 * 32 + m * 32;
            let total_size = fixed_header_size + ipp_size + ecp_size;

            // 4. Store Valid Configs
            if total_size <= max_proof_bytes {
                valid_configs.push(ProofConfig {
                    k,
                    d,
                    m,
                    n_padded,
                    padding,
                    exact_proof_size_bytes: total_size,
                });
            }
        }
    }

    if valid_configs.is_empty() {
        panic!("No configuration found fitting the proof size limit!");
    }

    // 5. SORTING LOGIC FOR SPEED
    valid_configs.sort_by(|a, b| {
        // Priority 1: Smallest k (Major speed factor)
        match a.k.cmp(&b.k) {
            std::cmp::Ordering::Equal => {
                // Priority 2: Smallest d (Shallowest fold = Fastest Prover)
                // This will prefer d=4 over d=10 if both fit in the size limit.
                match a.d.cmp(&b.d) {
                    std::cmp::Ordering::Equal => a.padding.cmp(&b.padding),
                    other => other,
                }
            }
            other => other,
        }
    });

    // Take top 3
    let top_configs: Vec<ProofConfig> = valid_configs.into_iter().take(3).collect();

    println!("Top {} Fastest Configs found:", top_configs.len());
    for (i, c) in top_configs.iter().enumerate() {
        println!("  #{}: k={}, d={}, m={} | Padding={} | Size={} bytes", 
                 i+1, c.k, c.d, c.m, c.padding, c.exact_proof_size_bytes);
    }
    
    top_configs
}

// Config calculation logic 
fn reconstruct_round_lengths_helper(mut n: usize, k: usize, d: usize) -> Vec<usize> {
    let mut lengths = Vec::with_capacity(d + 1);
    lengths.push(n);
    for _ in 0..d {
        let rem = n % k;
        let pad = if rem == 0 { 0 } else { k - rem };
        let n_padded = n + pad;
        n = n_padded / k;
        lengths.push(n);
    }
    lengths
}
/*// Finds the smallest n_pad such that n_pad >= n and n_pad is a multiple of k^num_rounds.
/// This matches the Partial Folding logic.
fn get_partial_fold_padding(n: usize, k: usize, num_rounds: usize) -> usize {
    assert!(k > 1, "k must be greater than 1.");

    let mut reduction_factor: usize = 1; 
    
    for _ in 0..num_rounds {
        if let Some(res) = reduction_factor.checked_mul(k) {
            reduction_factor = res;
        } else {
            panic!("Overflow calculating k^num_rounds. Reduce rounds or k.");
        }
    }

    if n == 0 {
        return reduction_factor;
    }

    // Pad to the next multiple of R
    let remainder = n % reduction_factor;
    if remainder == 0 {
        n
    } else {
        n + (reduction_factor - remainder)
    }
}

pub fn get_padded_values(n: usize, k_value: usize, num_rounds: usize) -> usize {
    assert!(n <= 1048576*2, "Input n exceeds maximum of 2^21");
    get_partial_fold_padding(n, k_value, num_rounds)
}
*/
///
struct KShuffleGadget {}

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(cs: &mut CS, x: &[Variable], y: &[Scalar], k_original: usize) {
        let one = Scalar::one();
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len(); // n_padded

        assert_eq!(x.len(), y.len());

        // 1. Calculate Cleartext Product (RHS)
        let mut prod_y = Scalar::one();
        for yi in y {
            prod_y *= *yi - z;
        }

        // 2. Calculate Circuit Product (LHS)
        // We accumulate the product into 'prev_lc'.
        
        // Initialization: Handle the first term (index 0)
        let mut prev_lc = if 0 >= k_original {
            // Padded zone (Index 0 is padding)
            cs.constrain(x[0] - Scalar::zero()); // Force x[0] = 0
            LinearCombination::from(-z)          // Term is (0 - z)
        } else {
            // Real zone
            x[0] - z
        };

        // Loop from 1 to k-1
        for i in 1..k {
            if i >= k_original {
                // --- PADDED ZONE ---
                // 1. Constraint: x[i] MUST be 0
                cs.constrain(x[i] - Scalar::zero());

                // 2. Operation: Multiply running product by (0 - z) = -z
                // Optimization: No new gate needed. Scale the LinearCombination.
                prev_lc = prev_lc * (-z);
            } else {
                // --- REAL ZONE ---
                // 1. Operation: Multiply running product by (x[i] - z)
                // This requires a multiplication gate.
                let term = x[i] - z;
                
                // multiply(left, right) -> (left, right, output)
                // We use output as the new accumulator
                let (_, _, out_var) = cs.multiply(prev_lc, term);
                prev_lc = LinearCombination::from(out_var);
            }
        }

        // 3. Final Constraint: LHS == RHS
        cs.constrain(prev_lc - prod_y);
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        input: &[Scalar],
        output: &[Scalar],
        //
        C1_prime: &[RistrettoPoint],
        C2_prime: &[RistrettoPoint],
        r_prime: Scalar,
        k_fold: usize,
        num_rounds: usize,
        
    ) -> Result<
        (
            R1CSProof,
            CompressedRistretto,
        ),
        R1CSError,
    > {
        // Apply a domain separator with the shuffle parameters to the transcript
        let k = input.len();
        let k_original =C1_prime.len();

        if k <=1 {
            return Err(R1CSError::InputLengthError);
        }
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut prover = Prover::new(&bp_gens, &pc_gens, transcript);

        // Construct blinding factors using an RNG.
        // Note: a non-example implementation would want to operate on existing commitments.
        let mut blinding_rng = rand::thread_rng();

        let v_blinding = Scalar::random(&mut blinding_rng);
        let (output_commitment, output_vars) = prover.commit_vec(&output, v_blinding, k_original);

        let mut cs = prover.finalize_inputs();
        

        Self::fill_cs(&mut cs, &output_vars, &input, k_original);
        

        let proof = cs.prove(C1_prime,C2_prime, r_prime, k_fold, num_rounds)?;

        Ok((proof, output_commitment))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        proof: &R1CSProof,
        input: &[Scalar],
        output_commitment: CompressedRistretto,
        //
        C1_prime: &[RistrettoPoint],
        C2_prime: &[RistrettoPoint],
        C: &[RistrettoPoint],
    ) -> Result<(), R1CSError> {
        // Apply a domain separator with the shuffle parameters to the transcript
        let k = input.len();
        transcript.commit_bytes(b"dom-sep", b"ShuffleProof");
        transcript.commit_bytes(b"k", Scalar::from(k as u64).as_bytes());

        let mut verifier = Verifier::new(&bp_gens, &pc_gens, transcript);
  
        let output_vars = verifier.commit_vec(output_commitment, k);


        let mut cs = verifier.finalize_inputs();
        let k_original = C1_prime.len();

        Self::fill_cs(&mut cs, &output_vars, &input, k_original);

        cs.verify(proof, C1_prime,C2_prime, C)
    }
}

fn kshuffle_prove_helper(num_rounds: usize, k: usize, k_original: usize, k_fold: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle Creation for n_padded = {}, k = {}, d = {}, rest = {}", k_original, k, k_fold, num_rounds, k / k_fold.pow(num_rounds as u32));

    c.bench_function(&label, move |b| {
        let mut rng = rand::thread_rng();

        // 1. Generate inputs
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k_original)
            .map(|_| Scalar::from(rng.gen_range(min, max)))
            .collect();
        

        // 2. Create Shuffle Permutation
        let mut indices: Vec<usize> = (0..k_original).collect();
        indices.shuffle(&mut rng);

        // 3. Apply Shuffle to create outputs
        let output: Vec<Scalar> = indices.iter().map(|&i| input[i]).collect();

        // 4. Generate Ciphertexts 
        let C1: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        let C2: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        
        /// 5. Shuffle and Re-randomize Ciphertexts
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(k, 1);
        let g = pc_gens.B;
        let h = pc_gens.B_blinding; 

        let mut C1_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C1[i]).collect();
        let mut C2_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C2[i]).collect();
        let mut r_prime = Scalar::zero();

        // 5. Randomize
        for (j, &i) in indices.iter().enumerate() {
            // Rerandomization scalar
            let r_i = Scalar::random(&mut rng);

            // Shuffle + rerandomize in place
            C1_prime[j] = C1[i] + g * r_i;
            C2_prime[j] = C2[i] + h * r_i;

            // Accumulate r_prime
            r_prime += r_i * input[i]; // i corresponds to output[j]
        }
        r_prime = -r_prime;

        // 6. EXPLICITLY PAD Scalars (Witnesses)
        // We pad to 'k' which is calculated as the nearest multiple
        let mut input_padded = input.clone();
        let mut output_padded = output.clone();
        input_padded.resize(k, Scalar::zero());
        output_padded.resize(k, Scalar::zero());

        
        b.iter(|| {
            let mut prover_transcript = Transcript::new(b"ShuffleTest");
            let (proof, out_commitment) = KShuffleGadget::prove(
                &pc_gens, 
                &bp_gens, 
                &mut prover_transcript, 
                &input_padded, 
                &output_padded,
                &C1_prime,
                &C2_prime,
                r_prime,
                k_fold,
                num_rounds,
            ).unwrap();
            //assert!(result.is_ok());

            // --- Serialization (Included in timing) ---
            let serialized_proof = bincode::serialize(&proof).unwrap();
            
            // Return proof size (optional)
            //criterion::black_box(serialized_proof);
            //criterion::black_box(out_commitment);
        })
    });
}


fn kshuffle_verify_helper(num_rounds: usize, k: usize, k_original: usize, k_fold: usize, c: &mut Criterion) {
    let label = format!("{}-shuffle Verification for n_padded = {}, k = {}, d = {}, rest = {}", k_original, k, k_fold, num_rounds, k / k_fold.pow(num_rounds as u32));

    c.bench_function(&label, move |b| {
        let mut rng = rand::thread_rng();

        // 1. Generate inputs (Real)
        let (min, max) = (0u64, std::u64::MAX);
        let input: Vec<Scalar> = (0..k_original)
            .map(|_| Scalar::from(rng.gen_range(min, max)))
            .collect();

        // 2. Create Shuffle Permutation
        let mut indices: Vec<usize> = (0..k_original).collect();
        indices.shuffle(&mut rng);

        // 3. Apply Shuffle to create outputs (Real)
        let output: Vec<Scalar> = indices.iter().map(|&i| input[i]).collect();

        // 4. Generate Ciphertexts (Real)
        let C1: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        let C2: Vec<RistrettoPoint> = (0..k_original)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        
        // 5. Shuffle and Re-randomize Ciphertexts
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(k, 1); // Gens must cover padded size 'k'
        let g = pc_gens.B;
        let h = pc_gens.B_blinding; 

        let mut C1_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C1[i]).collect();
        let mut C2_prime: Vec<RistrettoPoint> = indices.iter().map(|&i| C2[i]).collect();
        let mut r_prime = Scalar::zero();

        // Randomize
        for (j, &i) in indices.iter().enumerate() {
            let r_i = Scalar::random(&mut rng);

            // Shuffle + rerandomize in place
            C1_prime[j] = C1[i] + g * r_i;
            C2_prime[j] = C2[i] + h * r_i;

            // Accumulate r_prime
            r_prime += r_i * input[i]; 
        }
        r_prime = -r_prime;

        // 6. EXPLICITLY PAD Scalars (Witnesses)
        // We pad input/output to size 'k' (n_padded) for the circuit constraints
        let mut input_padded = input.clone();
        let mut output_padded = output.clone();
        input_padded.resize(k, Scalar::zero());
        output_padded.resize(k, Scalar::zero());

        // 7. Create Proof (Outside Benchmark)
        let mut prover_transcript = Transcript::new(b"ShuffleTest");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens, 
            &bp_gens, 
            &mut prover_transcript, 
            &input_padded, 
            &output_padded,
            &C1_prime,    // Real size (k_original)
            &C2_prime,    // Real size (k_original)
            r_prime,
            k_fold,
            num_rounds,
        ).expect("Proving failed");
        
        // 6. Compute the public statement for verification C = \prod_i C_i^e_i
            let mut C: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); 2];
            for i in 0..k_original {
                C[0] = C[0] + C1[i] * input[i];
                C[1] = C[1] + C2[i] * input[i];
            }

        // Serialize once for the benchmark
        let serialized_proof = bincode::serialize(&proof).unwrap();
        //println!("\n Serialized Proof Length: {} bytes", serialized_proof.len());
        //println!("Serialized Proof (first 64 bytes in hex): {:?}", &serialized_proof[0..64]);
        //println!("\n r_blinding in provers = {:?}", r_blinding);
        

        //let deserialized_proof_check: R1CSProof = bincode::deserialize(&serialized_proof).unwrap();
       
        //println!("Deserialized Proof (Debug): {:#?}", deserialized_proof_check);

        // Verify kshuffle proof
        b.iter(|| {

        // --- Deserialization (Included in timing) ---
            let deserialized_proof: R1CSProof = bincode::deserialize(&serialized_proof).unwrap();

            let mut verifier_transcript = Transcript::new(b"ShuffleTest");
            let result = KShuffleGadget::verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &deserialized_proof,        // Use the deserialized proof
                &input_padded,
                out_commitment,
                //
                &C1_prime, 
                &C2_prime, 
                &C,
            )
            ;
            assert!(result.is_ok());
        })
    });
}


struct Config {
    k: usize,
    d: usize,
    label: &'static str,
}

//128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576

fn kshuffle_verify_n(c: &mut Criterion) {
    let n_input = 1025;

    let configs = [
        Config { k: 4, d: 5, label: "Speed" },
    ];

    for config in configs.iter() {
       
        let rem = n_input % config.k;
        let pad_amt = if rem == 0 { 0 } else { config.k - rem };
        let n_padded = n_input + pad_amt;
        
        // Calculate the resulting 'm' (rest size) after d rounds of dynamic folding
        let lengths = reconstruct_round_lengths_helper(n_padded, config.k, config.d);
        let rest = *lengths.last().unwrap();

        kshuffle_verify_helper(
            config.d,
            n_padded, 
            n_input,
            config.k,       
            c
        );
    }
}


fn kshuffle_prove_n(c: &mut Criterion) {
    let n_input = 1048577; // Fixed Input N = 2^20 + 1 = 1048577

    println!("\n=======================================================");
    println!("  CASE: MULTIPLE OF k : N = {}", n_input);
    println!("  Format: [Tier] k | d | rest | padded | pad_amt | size");
    println!("=======================================================");

    let configs = [
        // --- TIER 1: SPEED (Shallow Tree, Huge Rest) ---
        Config { k: 2, d: 6, label: "Speed" },
        Config { k: 3, d: 4, label: "Speed" },
        Config { k: 4, d: 3, label: "Speed" },
        Config { k: 5, d: 3, label: "Speed" },

        // --- TIER 2: BALANCED (Moderate Tree, ~1k Rest) ---
        Config { k: 2, d: 10, label: "Balanced" },
        Config { k: 3, d: 6,  label: "Balanced" },
        Config { k: 4, d: 5,  label: "Balanced" },
        Config { k: 5, d: 4,  label: "Balanced" },

        // --- TIER 3: DEEP (Compact Tree, ~64 Rest) ---
        Config { k: 2, d: 14, label: "Deep" },
        Config { k: 3, d: 9,  label: "Deep" },
        Config { k: 4, d: 7,  label: "Deep" },
        Config { k: 5, d: 6,  label: "Deep" },

        // --- TIER 4: MAX (Full Recursion, ~1 Rest) ---
        Config { k: 2, d: 20, label: "Max" },
        Config { k: 3, d: 13, label: "Max" },
        Config { k: 4, d: 10, label: "Max" },
        Config { k: 5, d: 9,  label: "Max" },
    ];

    for config in configs.iter() {
        // 1. Calculate Powers and Dimensions
       
        let rem = n_input % config.k;
        let pad_amt = if rem == 0 { 0 } else { config.k - rem };
        let n_padded = n_input + pad_amt;
        
        // Calculate the resulting 'm' (rest size) after d rounds of dynamic folding
        let lengths = reconstruct_round_lengths_helper(n_padded, config.k, config.d);
        let rest = *lengths.last().unwrap();


        // 2. Exact Proof Size Calculation
        // A. Fixed R1CS Overhead: 13 points + 8 scalars + 2 u64 lengths
        let r1cs_overhead = (13 + 8) * 32 + 16;

        // B. IPP Proof Size
        //    (3 headers + d rounds of (2k-2) points + 2 vectors of size rest) * 32
        let ipp_points = if config.d > 0 { config.d * (2 * config.k - 2) } else { 0 };
        let ipp_size = (3 + ipp_points + 2 * rest) * 32;

        // C. Batched ECP Size
        //    (3 headers + d rounds of (2k-2)*2 points + 1 vector of size rest) * 32
        let ecp_points = if config.d > 0 { config.d * (2 * config.k - 2) * 2 } else { 0 };
        let ecp_size = (3 + ecp_points + rest) * 32;

        let total_bytes = r1cs_overhead + ipp_size + ecp_size;

        // 3. Print the Configuration Block
        println!("\n-------------------------------------------------------");
        println!("Case: MULTIPLE OF k: {} (k={})", config.label, config.k);
        println!("-------------------------------------------------------");
        println!("  k              : {}", config.k);
        println!("  d              : {}", config.d);
        println!("  rest           : {}", rest);
        println!("  n_padded       : {}", n_padded);
        println!("  Padding        : {}", pad_amt);
        println!("  Proof (bytes)  : {}", total_bytes);
        println!("  Prover time    : [Running Criterion...]"); 

        // 4. Run Benchmark
        // The helper needs to use the BenchmarkId to tag the result correctly 
        // in the Criterion report.
        kshuffle_prove_helper(
            config.d,
            n_padded, 
            n_input,
            config.k,       
            c
        );
    }
}


criterion_group! {
    name = kshuffle_verify;
    config = Criterion::default().sample_size(2)
            .measurement_time(std::time::Duration::from_secs(10)); 
    targets =
    kshuffle_verify_n,
}

criterion_group! {
    name = kshuffle_prove;
    config = Criterion::default().sample_size(2)
            .measurement_time(std::time::Duration::from_secs(10)); 
    targets =
    kshuffle_prove_n,
}

criterion_main!( kshuffle_prove);//kshuffle_prove, kshuffle_verify

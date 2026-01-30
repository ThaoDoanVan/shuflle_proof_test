#![allow(non_snake_case)]

use clear_on_drop::clear::Clear;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;
use inner_product_proof::inner_product;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::K_BulletProof;
use inner_product_proof::batched_eCP;
use transcript::TranscriptProtocol;
use std::iter;


// For testing 
use curve25519_dalek::traits::VartimeMultiscalarMul;



/// An entry point for creating a R1CS proof.
///
/// The lifecycle of a `Prover` is as follows. The proving code
/// commits high-level variables and their blinding factors `(v, v_blinding)`,
/// `Prover` generates commitments, adds them to the transcript and returns
/// the corresponding variables.
///
/// After all variables are committed, the proving code calls `finalize_inputs`,
/// which consumes `Prover` and returns `ProverCS`.
/// The proving code then allocates low-level variables and adds constraints to the `ProverCS`.
///
/// When all constraints are added, the proving code calls `prove`
/// on the instance of the constraint system and receives the complete proof.
pub struct Prover<'a, 'b> {
    /// Number of high-level variables
    m: u64,

    /// Constraint system implementation
    cs: ProverCS<'a, 'b>,
}

/// A [`ConstraintSystem`] implementation for use by the prover.
pub struct ProverCS<'a, 'b> {
    transcript: &'a mut Transcript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    /// The constraints accumulated so far.
    constraints: Vec<LinearCombination>,
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<Scalar>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<Scalar>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<Scalar>,
    /// High-level witness data (value openings to V commitments)
    v: Vec<Scalar>,
    /// High-level witness data (blinding openings to V commitments)
    v_blinding: Scalar,
}

/// Overwrite secrets with null bytes when they go out of scope.
impl<'a, 'b> Drop for ProverCS<'a, 'b> {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.clear();

        // Important: due to how ClearOnDrop auto-implements InitializableFromZeroed
        // for T: Default, calling .clear() on Vec compiles, but does not
        // clear the content. Instead, it only clears the Vec's header.
        // Clearing the underlying buffer item-by-item will do the job, but will
        // keep the header as-is, which is fine since the header does not contain secrets.
        for e in self.a_L.iter_mut() {
            e.clear();
        }
        for e in self.a_R.iter_mut() {
            e.clear();
        }
        for e in self.a_O.iter_mut() {
            e.clear();
        }
        // XXX use ClearOnDrop instead of doing the above
    }
}

impl<'a, 'b> ConstraintSystem for ProverCS<'a, 'b> {
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::one()));
        right.terms.push((r_var, -Scalar::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let (l, r, o) = assign_fn()?;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Prover<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut Transcript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Prover {
            m: 0,
            cs: ProverCS {
                pc_gens,
                bp_gens,
                transcript,
                v: Vec::new(),
                v_blinding: Scalar::zero(),
                constraints: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
            },
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitment to the external variable for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    
   
    
    pub fn commit_vec(
        &mut self,
        v: &[Scalar],
        v_blinding: Scalar,
        k_original: usize,
    ) -> (CompressedRistretto, Vec<Variable>) {
        let start_index = self.m as usize;
        let n_padded = v.len();

        // Safety check
        assert!(k_original <= n_padded);

        // Update prover state
        self.m += n_padded as u64;
        for &v_i in v.iter() {
            self.cs.v.push(v_i);
        }
        //self.cs.v_blinding.push(v_blinding);
        self.cs.v_blinding = v_blinding;


        // Compute the vector Pedersen commitment:
        // V = <v_i, G_i> + v_blinding * B_blinding
       
        // OPTIMIZED MSM:
        // V = v_blinding * B_blinding + sum_{0..k_original} (v_i * G_i)
        // We skip sum_{k_original..n_padded} because v_i is 0.
        //TODO: recover V for self.cs.bp_gens.G(k_original, 1
        /*let V = RistrettoPoint::multiscalar_mul(
            iter::once(&v_blinding)
                .chain(v[0..k_original].iter()), 
            iter::once(&self.cs.pc_gens.B_blinding)
                .chain(self.cs.bp_gens.G(k_original, 1)), 
        )
        .compress();*/
        let V = RistrettoPoint::multiscalar_mul(
            iter::once(&v_blinding)
                .chain(v.iter()), 
            iter::once(&self.cs.pc_gens.B_blinding)
                .chain(self.cs.bp_gens.G(n_padded, 1)), 
        )
        .compress();

        
        // Add the commitment to the transcript
        self.cs.transcript.commit_point(b"V", &V);

        // Build committed variables for the FULL range
        let vars: Vec<Variable> = (start_index..start_index + n_padded)
            .map(|i| Variable::Committed(i))
            .collect();


        (V, vars)
    }

    /// Consume the `Prover`, provide the `ConstraintSystem` implementation to the closure,
    /// and produce a proof.
    pub fn finalize_inputs(self) -> ProverCS<'a, 'b> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.cs.transcript.commit_u64(b"m", self.m);
        self.cs
    }
}



impl<'a, 'b> ProverCS<'a, 'b> {
    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![Scalar::zero(); n];
        let mut wR = vec![Scalar::zero(); n];
        let mut wO = vec![Scalar::zero(); n];
        let mut wV = vec![Scalar::zero(); m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                coeff
                    * match var {
                        Variable::MultiplierLeft(i) => self.a_L[*i],
                        Variable::MultiplierRight(i) => self.a_R[*i],
                        Variable::MultiplierOutput(i) => self.a_O[*i],
                        Variable::Committed(i) => self.v[*i],
                        Variable::One() => Scalar::one(),
                    }
            })
            .sum()
    }

    pub fn prove(
    mut self,
    C1_prime: &[RistrettoPoint],
    C2_prime: &[RistrettoPoint],
    r_prime: Scalar,
    k_fold: usize,
    num_rounds:usize,
) -> Result<R1CSProof, R1CSError> {
    // Standard Imports
    use inner_product_proof::inner_product;
    use rand::thread_rng;
    use std::iter;
    use util;

    // -----------------------------------------------------------------------------
    // 0. Setup
    // -----------------------------------------------------------------------------
    let n = self.a_L.len();
    let k = self.v.len();
    
    //let padded_n = k.next_power_of_two();
    //let padded_n = k;//because i need to pad from fill_cs, i.e. before doing proof already ; padded_n =next_power_of_k(n, k_fold);

    if self.bp_gens.gens_capacity < k {
        return Err(R1CSError::InvalidGeneratorsLength);
    }
    
    // Single-party circuit proof, so party index is 0
    let gens = self.bp_gens.share(0);

    // -----------------------------------------------------------------------------
    // 1. Transcript & RNG
    // -----------------------------------------------------------------------------
    let mut rng = {
        let mut builder = self.transcript.build_rng();
        builder = builder.commit_witness_bytes(b"v_blinding", self.v_blinding.as_bytes());
        builder.finalize(&mut thread_rng())
    };

    // -----------------------------------------------------------------------------
    // 2. Circuit Commitment
    // -----------------------------------------------------------------------------
    let i_blinding = Scalar::random(&mut rng);
    let o_blinding = Scalar::random(&mut rng);
    let s_blinding = Scalar::random(&mut rng);

    // OPTIMIZATION: Pre-allocate memory to avoid re-allocations
    let mut s_L = Vec::with_capacity(n);
    let mut s_R = Vec::with_capacity(n);
    for _ in 0..n {
        s_L.push(Scalar::random(&mut rng));
        s_R.push(Scalar::random(&mut rng));
    }

    let A_I = RistrettoPoint::multiscalar_mul(
        iter::once(&i_blinding).chain(self.a_L.iter()).chain(self.a_R.iter()),
        iter::once(&self.pc_gens.B_blinding).chain(gens.G(n)).chain(gens.H(n)),
    ).compress();

    let A_O = RistrettoPoint::multiscalar_mul(
        iter::once(&o_blinding).chain(self.a_O.iter()),
        iter::once(&self.pc_gens.B_blinding).chain(gens.G(n)),
    ).compress();

    let S = RistrettoPoint::multiscalar_mul(
        iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
        iter::once(&self.pc_gens.B_blinding).chain(gens.G(n)).chain(gens.H(n)),
    ).compress();

    self.transcript.commit_point(b"A_I", &A_I);
    self.transcript.commit_point(b"A_O", &A_O);
    self.transcript.commit_point(b"S", &S);

    // -----------------------------------------------------------------------------
    // 3. Polynomials
    // -----------------------------------------------------------------------------
    let y = self.transcript.challenge_scalar(b"y");
    let z = self.transcript.challenge_scalar(b"z");

    let (wL, wR, wO, wV) = self.flattened_constraints(&z);

    // OPTIMIZATION: Compute exp_y_inv. 
    // We fuse H_prime calculation later to avoid iterating this vector multiple times.
    let y_inv = y.invert();
    let exp_y_inv: Vec<Scalar> = util::exp_iter(y_inv).take(k).collect();

    // Note: If VecPoly3 can be initialized with capacity, do so. 
    // Otherwise, we rely on standard initialization.
    let mut l_poly = util::VecPoly3::zero(n);
    let mut r_poly = util::VecPoly3::zero(n);
    let mut exp_y = Scalar::one();

    for i in 0..n {
        l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
        l_poly.2[i] = self.a_O[i];
        l_poly.3[i] = s_L[i];

        r_poly.0[i] = wO[i] - exp_y;
        r_poly.1[i] = exp_y * self.a_R[i] + wL[i];
        r_poly.3[i] = exp_y * s_R[i];

        exp_y *= y;
    }

    let t_poly = util::VecPoly3::special_inner_product(&l_poly, &r_poly);

    // T Commitments
    let t_blindings = [
        Scalar::random(&mut rng), // 1
        Scalar::random(&mut rng), // 3
        Scalar::random(&mut rng), // 4
        Scalar::random(&mut rng), // 5
        Scalar::random(&mut rng), // 6
    ];

    let T_1 = self.pc_gens.commit(t_poly.t1, t_blindings[0]).compress();
    let T_3 = self.pc_gens.commit(t_poly.t3, t_blindings[1]).compress();
    let T_4 = self.pc_gens.commit(t_poly.t4, t_blindings[2]).compress();
    let T_5 = self.pc_gens.commit(t_poly.t5, t_blindings[3]).compress();
    let T_6 = self.pc_gens.commit(t_poly.t6, t_blindings[4]).compress();

    // T2 Calculation
    let t_2_blinding = Scalar::random(&mut rng);
    let t_2: Scalar = wV.iter().zip(self.v.iter()).map(|(c, v)| c * v).sum();
    let T_2 = self.pc_gens.commit(t_2, t_2_blinding).compress();

    self.transcript.commit_point(b"T_1", &T_1);
    self.transcript.commit_point(b"T_3", &T_3);
    self.transcript.commit_point(b"T_4", &T_4);
    self.transcript.commit_point(b"T_5", &T_5);
    self.transcript.commit_point(b"T_6", &T_6);
    self.transcript.commit_point(b"T_2", &T_2);

    let x = self.transcript.challenge_scalar(b"x");

    // Evaluate T(x)
    let t_x = t_poly.eval(x);
    let t_x_blinding = util::Poly6 {
        t1: t_blindings[0], t2: t_2_blinding, t3: t_blindings[1], 
        t4: t_blindings[2], t5: t_blindings[3], t6: t_blindings[4],
    }.eval(x);

    // Evaluate l and r vectors
    let mut l_vec = l_poly.eval(x);
    let mut r_vec = r_poly.eval(x);
    
    // OPTIMIZATION: Immediate resize with zero-fill.
    // This is cheap, but we will optimize the Usage of these zeros later.
    l_vec.resize(k, Scalar::zero());
    r_vec.resize(k, Scalar::zero());

    // Fix r_vec padding (-y^n term)
    // Resume exp_y from where loop left off
    for i in n..k {
        r_vec[i] = -exp_y;
        exp_y *= y;
    }

    let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

    self.transcript.commit_scalar(b"t_x", &t_x);
    self.transcript.commit_scalar(b"t_x_blinding", &t_x_blinding);
    self.transcript.commit_scalar(b"e_blinding", &e_blinding);

    // -----------------------------------------------------------------------------
    // 4. Consistency Setup
    // -----------------------------------------------------------------------------
    let s_bl_prime = Scalar::random(&mut rng);
    let rnd = Scalar::random(&mut rng);
    let k_original = C1_prime.len();

    // OPTIMIZATION: pre-allocate
    let mut s_L_prime = Vec::with_capacity(k);
    
    for _ in 0..k_original { 
        s_L_prime.push(Scalar::random(&mut rng)); 
    }

    // Optimization: Only multiply up to k_original (since rest of s_L_prime is 0)
    let S_prime = RistrettoPoint::multiscalar_mul(
        iter::once(&s_bl_prime).chain(s_L_prime[0..k_original].iter()),
        iter::once(&self.pc_gens.B_blinding).chain(gens.G(k_original)),
    ).compress();

    let S1_prime = RistrettoPoint::multiscalar_mul(
        iter::once(&rnd).chain(s_L_prime[0..k_original].iter()),
        iter::once(&self.pc_gens.B).chain(C1_prime.iter()),
    ).compress();

    let S2_prime = RistrettoPoint::multiscalar_mul(
        iter::once(&rnd).chain(s_L_prime[0..k_original].iter()),
        iter::once(&self.pc_gens.B_blinding).chain(C2_prime.iter()),
    ).compress();


    // Polynomials lc(x) and rc(x)
    let mut lc_poly = util::VecPoly1::zero(k);
    let mut rc_poly = util::VecPoly1::zero(k);

    // Padding Zero to match k size of lc_poly
    for _ in k_original..k {
        s_L_prime.push(Scalar::zero());
    }
    for i in 0..k {
        lc_poly.0[i] = self.v[i];
        lc_poly.1[i] = s_L_prime[i];
        rc_poly.0[i] = wV[i];
    }

    let tc_poly = lc_poly.inner_product(&rc_poly);
    let t1_bl_prime = Scalar::random(&mut rng);
    let T_1_prime = self.pc_gens.commit(tc_poly.1, t1_bl_prime).compress();
    let tc_bl_poly = util::Poly2(t_2_blinding, t1_bl_prime, Scalar::zero());

    self.transcript.commit_point(b"S_prime", &S_prime);
    self.transcript.commit_point(b"T_1_prime", &T_1_prime);
    self.transcript.commit_point(b"S1_prime", &S1_prime);
    self.transcript.commit_point(b"S2_prime", &S2_prime);

    let x_prime = self.transcript.challenge_scalar(b"x_prime");

    let tc_x = tc_poly.eval(x_prime);
    let tc_x_blinding = tc_bl_poly.eval(x_prime);
    let ec_blinding = self.v_blinding + s_bl_prime * x_prime;
    let r_blinding = r_prime + rnd * x_prime;

    self.transcript.commit_scalar(b"tc_x", &tc_x);
    self.transcript.commit_scalar(b"tc_x_blinding", &tc_x_blinding);
    self.transcript.commit_scalar(b"ec_blinding", &ec_blinding);
    self.transcript.commit_scalar(b"r_blinding", &r_blinding);

    let lc_vec = lc_poly.eval(x_prime);
    let rc_vec = rc_poly.eval(x_prime);

    // -----------------------------------------------------------------------------
    // 5. Aggregation Protocol (Math Optimized)
    // -----------------------------------------------------------------------------
    
    // OPTIMIZATION: Smart t_cross calculation.
    // Instead of creating padded vectors and dot-producting zeros, 
    // we only dot-product the valid range (0..k).
    // t_cross = <l, rc_pad> + <lc_pad, r>  
    // => <l[0..k], rc> + <lc, r[0..k]>
    let t_cross = inner_product(&l_vec[0..k], &rc_vec) 
                + inner_product(&lc_vec, &r_vec[0..k]);

    self.transcript.commit_scalar(b"t_cross", &t_cross);
    let x_ipp = self.transcript.challenge_scalar(b"x_ipp");

    // OPTIMIZATION: Single-pass Aggregation
    // We construct l_agg and r_agg directly, handling the padding logic 
    // inside the loop. This removes the need for `lc_vec_pad` allocations entirely.
    let mut l_agg = Vec::with_capacity(k);
    let mut r_agg = Vec::with_capacity(k);

    // 1. Valid Range (0..k): Mix l/r with lc/rc
    for i in 0..k {
        l_agg.push(l_vec[i] + x_ipp * lc_vec[i]);
        r_agg.push(r_vec[i] + x_ipp * rc_vec[i]);
    }

    // 2. Padding Range (k..padded_n): lc/rc are effectively 0, so just copy l/r
    //if padded_n > k {
    //    l_agg.extend_from_slice(&l_vec[k..padded_n]);
    //    r_agg.extend_from_slice(&r_vec[k..padded_n]);
    //}

    let w_agg = self.transcript.challenge_scalar(b"w_agg");
    let Q_agg = w_agg * self.pc_gens.B;

    // OPTIMIZATION: Fuse H_prime creation
    // We zip directly with the generator iterator to avoid creating an intermediate `H_padded` vector.
    // This saves one huge memory allocation and copy.
    let H_prime: Vec<RistrettoPoint> = gens.H(k)
        .zip(exp_y_inv.iter())
        .map(|(H_i, exp_i)| H_i * exp_i)
        .collect();

    /*let ipp_proof = K_BulletProof::create(
        self.transcript,
        k_fold,
        gens.G(padded_n).cloned().collect(),
        H_prime,
        Q_agg,
        l_agg,
        r_agg,
        num_rounds,
    );*/

    // OPTIMIZATION: Pass references to slices instead of cloning large vectors
    let ipp_proof = K_BulletProof::create(
        self.transcript,
        k_fold,
        &self.bp_gens.G_vec[0][0..k], // Zero-copy: Pass slice from BulletproofGens directly
        &H_prime,                         // Pass reference
        Q_agg,
        &l_agg,                          
        &r_agg,                           
        num_rounds,
    );

    // -----------------------------------------------------------------------------
    // 6. Batched ECP Protocol
    // -----------------------------------------------------------------------------
    let chall_batched_ecp = self.transcript.challenge_scalar(b"chall_batched_ecp");

    let C_agg: Vec<RistrettoPoint> = C1_prime
        .iter()
        .zip(C2_prime.iter())
        .map(|(c1, c2)| c1 + c2 * chall_batched_ecp)
        .collect();

    let ecp_batched = batched_eCP::create(
        self.transcript,
        k_fold,
        //gens.G(k).cloned().collect(),
        &self.bp_gens.G_vec[0][0..k], // Zero-copy
        &C_agg,
        &lc_vec,
        num_rounds,
    );
    //let test = self.transcript.challenge_scalar(b"test");
    //println!("test P = {:?}", test);

    
    // -----------------------------------------------------------------------------
    // 7. Cleanup
    // -----------------------------------------------------------------------------
    for e in s_L.iter_mut() { e.clear(); }
    for e in s_R.iter_mut() { e.clear(); }

    Ok(R1CSProof {
        A_I, A_O, S,
        T_1, T_2, T_3, T_4, T_5, T_6,
        t_x, t_x_blinding, e_blinding,
        ipp_proof,
        S_prime, T_1_prime,
        tc_x, tc_x_blinding, ec_blinding,
        t_cross,
        S1_prime, S2_prime, r_blinding,
        ecp_batched,
    })
}

}
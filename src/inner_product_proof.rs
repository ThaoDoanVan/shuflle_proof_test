#![allow(non_snake_case)]
#![doc= include_str!("../docs/inner-product-protocol.md")]

use std::borrow::Borrow;
use std::iter;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use merlin::Transcript;

use errors::ProofError;
use transcript::TranscriptProtocol;
use std::convert::TryInto;

use curve25519_dalek::traits::IsIdentity;

// =========================================================================
//  Helpers
// =========================================================================

fn scalar_pow(base: Scalar, mut exp: u64) -> Scalar {
    let mut result = Scalar::one();
    let mut b = base;
    while exp > 0 {
        if (exp & 1) == 1 {
            result *= b;
        }
        b *= b;
        exp >>= 1;
    }
    result
}

fn reconstruct_round_lengths(mut n: usize, k: usize, d: usize) -> Vec<usize> {
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

#[derive(Clone, Debug)]
pub struct InnerProductProof {
    pub(crate) L_vec: Vec<CompressedRistretto>,
    pub(crate) R_vec: Vec<CompressedRistretto>,
    pub(crate) a: Scalar,
    pub(crate) b: Scalar,
}

impl InnerProductProof {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &RistrettoPoint,
        Hprime_factors: &[Scalar],
        mut G_vec: Vec<RistrettoPoint>,
        mut H_vec: Vec<RistrettoPoint>,
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>,
    ) -> InnerProductProof {
        
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        
        if n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_L.iter()
                    .cloned()
                    .chain(
                        b_R.iter()
                            .zip(Hprime_factors[0..n].into_iter())
                            .map(|(b_R_i, y_i)| b_R_i * y_i),
                    )
                    .chain(iter::once(c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_R.iter()
                    .cloned()
                    .chain(
                        b_L.iter()
                            .zip(Hprime_factors[n..2 * n].into_iter())
                            .map(|(b_L_i, y_i)| b_L_i * y_i),
                    )
                    .chain(iter::once(c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)),
            )
            .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.commit_point(b"L", &L);
            transcript.commit_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u_inv, u], &[G_L[i], G_R[i]]);
                H_L[i] = RistrettoPoint::vartime_multiscalar_mul(
                    &[u * Hprime_factors[i], u_inv * Hprime_factors[n + i]],
                    &[H_L[i], H_R[i]],
                )
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            
            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L = RistrettoPoint::vartime_multiscalar_mul(
                a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)),
            )
            .compress();

            let R = RistrettoPoint::vartime_multiscalar_mul(
                a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)),
            )
            .compress();

            L_vec.push(L);
            R_vec.push(R);

            transcript.commit_point(b"L", &L);
            transcript.commit_point(b"R", &R);

            let u = transcript.challenge_scalar(b"u");
            let u_inv = u.invert();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u_inv, u], &[G_L[i], G_R[i]]);
                H_L[i] = RistrettoPoint::vartime_multiscalar_mul(&[u, u_inv], &[H_L[i], H_R[i]]);
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductProof {
            L_vec: L_vec,
            R_vec: R_vec,
            a: a[0],
            b: b[0],
        }
    }

    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.commit_point(b"L", L);
            transcript.commit_point(b"R", R);
            challenges.push(transcript.challenge_scalar(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        let allinv = Scalar::batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.
        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }
        
        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<I>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        Hprime_factors: I,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        G: &[RistrettoPoint],
        H: &[RistrettoPoint],
    ) -> Result<(), ProofError>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let a_times_s = s.iter().map(|s_i| self.a * s_i).take(G.len());

        let inv_s = s.iter().rev();

        let h_times_b_div_s = Hprime_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -ui);

        let Ls = self
            .L_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let Rs = self
            .R_vec
            .iter()
            .map(|p| p.decompress().ok_or(ProofError::VerificationError))
            .collect::<Result<Vec<_>, _>>()?;

        let expect_P = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(self.a * self.b)
                .chain(a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq),
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(Ls.iter())
                .chain(Rs.iter()),
        );

        if expect_P == *P {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 2) * 32
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) 32-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.extend_from_slice(l.as_bytes());
            buf.extend_from_slice(r.as_bytes());
        }
        buf.extend_from_slice(self.a.as_bytes());
        buf.extend_from_slice(self.b.as_bytes());
        buf
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+2\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n\\) points are not valid compressed Ristretto points,
    /// * any of 2 scalars are not canonical scalars modulo Ristretto group order.
    pub fn from_bytes(slice: &[u8]) -> Result<InnerProductProof, ProofError> {
        let b = slice.len();
        if b % 32 != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / 32;
        if num_elements < 2 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 2) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 2) / 2;
        if lg_n >= 32 {
            return Err(ProofError::FormatError);
        }

        use util::read32;

        let mut L_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<CompressedRistretto> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = 2 * i * 32;
            L_vec.push(CompressedRistretto(read32(&slice[pos..])));
            R_vec.push(CompressedRistretto(read32(&slice[pos + 32..])));
        }

        let pos = 2 * lg_n * 32;
        let a =
            Scalar::from_canonical_bytes(read32(&slice[pos..])).ok_or(ProofError::FormatError)?;
        let b = Scalar::from_canonical_bytes(read32(&slice[pos + 32..]))
            .ok_or(ProofError::FormatError)?;

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}


// =========================================================================
//  K_BulletProof (IPA with Iterative Padding)
// =========================================================================

#[derive(Clone, Debug)]
pub struct K_BulletProof {
    pub(crate) k: usize,
    pub(crate) U_vecs: Vec<Vec<CompressedRistretto>>,
    pub(crate) a_final: Vec<Scalar>,
    pub(crate) b_final: Vec<Scalar>,
}
  
impl K_BulletProof {   
    pub fn create(
        transcript: &mut Transcript,
        k: usize, 
        g_vec: &[RistrettoPoint], 
        h_vec: &[RistrettoPoint], 
        Q_point: RistrettoPoint, 
        a_vec: &[Scalar],         
        b_vec: &[Scalar],       
        num_rounds: usize, 
    ) -> K_BulletProof {
        let n = a_vec.len();
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);
        assert_eq!(b_vec.len(), n);
        assert!(k > 1, "k must be greater than 1");

        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut g_curr = g_vec.to_vec(); 
        let mut h_curr = h_vec.to_vec();
        let mut a_curr = a_vec.to_vec();
        let mut b_curr = b_vec.to_vec();

        let mut U_vecs: Vec<Vec<CompressedRistretto>> = Vec::with_capacity(num_rounds);

        let mut scalars_l: Vec<Scalar> = Vec::with_capacity(2 * n);
        let mut points_l: Vec<RistrettoPoint> = Vec::with_capacity(2 * n);
        let mut scalars_neg_l: Vec<Scalar> = Vec::with_capacity(2 * n);
        let mut points_neg_l: Vec<RistrettoPoint> = Vec::with_capacity(2 * n);

        let mut g_points_col: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); k];
        let mut h_points_col: Vec<RistrettoPoint> = vec![RistrettoPoint::default(); k];

        let mut n_j = n; 

        for j in 0..num_rounds {
            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(std::iter::repeat(Scalar::zero()).take(pad));
                b_curr.extend(std::iter::repeat(Scalar::zero()).take(pad));
                g_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                h_curr.extend(std::iter::repeat(RistrettoPoint::default()).take(pad));
                n_j += pad;
            }

            let m_j = n_j / k; 

            let a_splits: Vec<&[Scalar]> = a_curr.chunks(m_j).collect();
            let b_splits: Vec<&[Scalar]> = b_curr.chunks(m_j).collect();
            let g_splits: Vec<&[RistrettoPoint]> = g_curr.chunks(m_j).collect();
            let h_splits: Vec<&[RistrettoPoint]> = h_curr.chunks(m_j).collect();

            let mut U_pos_compressed: Vec<CompressedRistretto> = Vec::with_capacity(k - 1);
            let mut U_neg_compressed: Vec<CompressedRistretto> = Vec::with_capacity(k - 1);
            
            for l in 1..k { 
                let mut v_pos_l = Scalar::zero();
                let mut v_neg_l = Scalar::zero();
                scalars_l.clear(); points_l.clear();
                scalars_neg_l.clear(); points_neg_l.clear();

                for i in 0..(k - l) {
                    v_pos_l += inner_product(a_splits[i], b_splits[i + l]);
                    scalars_l.extend_from_slice(a_splits[i]);
                    points_l.extend_from_slice(g_splits[i+l]);
                    scalars_l.extend_from_slice(b_splits[i+l]);
                    points_l.extend_from_slice(h_splits[i]);

                    v_neg_l += inner_product(a_splits[i + l], b_splits[i]);
                    scalars_neg_l.extend_from_slice(a_splits[i+l]);
                    points_neg_l.extend_from_slice(g_splits[i]);
                    scalars_neg_l.extend_from_slice(b_splits[i]);
                    points_neg_l.extend_from_slice(h_splits[i+l]);
                }
                
                let U_l = RistrettoPoint::vartime_multiscalar_mul(scalars_l.iter(), points_l.iter()) 
                        + v_pos_l * Q_point;
                U_pos_compressed.push(U_l.compress());

                let U_neg_l = RistrettoPoint::vartime_multiscalar_mul(scalars_neg_l.iter(), points_neg_l.iter()) 
                            + v_neg_l * Q_point;
                U_neg_compressed.push(U_neg_l.compress());
            }

            let mut U_vec_round = U_pos_compressed;
            U_vec_round.extend(U_neg_compressed);
            
            for (idx, point_compressed) in U_vec_round.iter().enumerate() {
                 transcript.append_message(b"U_round", &(j as u64).to_le_bytes());
                 transcript.append_message(b"U_index", &(idx as u64).to_le_bytes());
                 transcript.commit_point(b"U_point", &point_compressed);
            }
            U_vecs.push(U_vec_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(j as u64).to_le_bytes());
            let c = transcript.challenge_scalar(b"challenge_separator");
            let c_inv = c.invert();

            let mut a_new = vec![Scalar::zero(); m_j];
            let mut b_new = vec![Scalar::zero(); m_j];
            let mut g_new = vec![RistrettoPoint::default(); m_j];
            let mut h_new = vec![RistrettoPoint::default(); m_j];

            let mut c_powers_a: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow_y = Scalar::one();
            for _ in 0..k { c_powers_a.push(c_pow_y); c_pow_y *= c; }

            let mut c_powers_b: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow_x = Scalar::one(); 
            for _ in 1..k { c_pow_x *= c; }
            for _ in 0..k { c_powers_b.push(c_pow_x); c_pow_x *= c_inv; }

            for j_item in 0..m_j {
                let mut a_j_acc = Scalar::zero();
                let mut b_j_acc = Scalar::zero();
                for i in 0..k {
                    a_j_acc += a_splits[i][j_item] * c_powers_a[i];
                    b_j_acc += b_splits[i][j_item] * c_powers_b[i];
                }
                a_new[j_item] = a_j_acc;
                b_new[j_item] = b_j_acc;
            }

            let g_scalars = &c_powers_b;
            let h_scalars = &c_powers_a;
            
            for j_item in 0..m_j {
                for i in 0..k {
                    g_points_col[i] = g_splits[i][j_item];
                    h_points_col[i] = h_splits[i][j_item];
                }
                g_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(g_scalars.iter(), g_points_col.iter());
                h_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(h_scalars.iter(), h_points_col.iter());
            }

            a_curr = a_new;
            b_curr = b_new;
            g_curr = g_new;
            h_curr = h_new;

            n_j = m_j;
        }

        K_BulletProof {
            k,
            U_vecs,
            a_final: a_curr,
            b_final: b_curr,
        }
    }

    pub fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(
        Vec<Scalar>,    
        Vec<Scalar>,    
        Scalar,         
        Scalar,         
        Vec<Scalar>,    
    ), ProofError> {
        
        let k = self.k;
        if n == 0 { return Err(ProofError::InvalidGeneratorsLength); }
        let d = self.U_vecs.len();

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap(); 

        if self.a_final.len() != m || self.b_final.len() != m {
             return Err(ProofError::VerificationError);
        }

        transcript.append_message(b"protocol-name", b"k_bullet_delay");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);
        
        for r in 0..d {
            for i_list in 0..(2 * k - 2) {
                transcript.append_message(b"U_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"U_index", &(i_list as u64).to_le_bytes());
                transcript.commit_point(b"U_point", &self.U_vecs[r][i_list]);
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(transcript.challenge_scalar(b"challenge_separator"));
        }

        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);
        
        let mut s_P = Scalar::one();
        let k_minus_1_exp = (k - 1) as u64;
        let mut c_k_minus_1_products = vec![Scalar::one(); d]; 
        let mut product_so_far = Scalar::one();
        for r in (0..d).rev() {
            let c_k_minus_1 = scalar_pow(challenges[r], k_minus_1_exp); 
            c_k_minus_1_products[r] = product_so_far; 
            product_so_far *= c_k_minus_1;
        }
        s_P = product_so_far;

        let mut s_g_full = self.a_final.clone(); 
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = Scalar::one();
            for _ in 0..k { block.push(val); val *= c_inv; }

            let mut next_s = Vec::with_capacity(s_g_full.len() * k);
            for b in block.iter() {
                for val in s_g_full.iter() { next_s.push(val * b); }
            }
            
            next_s.truncate(round_lengths[r]);
            s_g_full = next_s;
        }
        for x in s_g_full.iter_mut() { *x *= s_P; }

        let mut s_h_full = self.b_final.clone(); 
        for r in (0..d).rev() {
            let c = challenges[r];
            let mut block = Vec::with_capacity(k);
            let mut val = Scalar::one();
            for _ in 0..k { block.push(val); val *= c; }

            let mut next_s = Vec::with_capacity(s_h_full.len() * k);
            for b in block.iter() {
                for val in s_h_full.iter() { next_s.push(val * b); }
            }

            next_s.truncate(round_lengths[r]);
            s_h_full = next_s;
        }
    
        let s_Q_final = inner_product(&self.a_final, &self.b_final); 

        let mut s_U: Vec<Scalar> = Vec::with_capacity(d * (2*k - 2));
        for r in 0..d { 
            let c_r = challenges[r];
            let suffix_prod = c_k_minus_1_products[r];
            for l in 1..k { 
                let exp = (k - 1 - l) as u64;
                s_U.push(scalar_pow(c_r, exp) * suffix_prod); 
            }
            for l in 1..k { 
                let exp = (k - 1 + l) as u64; 
                s_U.push(scalar_pow(c_r, exp) * suffix_prod); 
            }
        }
        
        Ok((s_g_full, s_h_full, s_Q_final, s_P, s_U))
    }

    #[allow(dead_code)]
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        g_vec: &Vec<RistrettoPoint>,
        h_vec: &Vec<RistrettoPoint>,
        Q_point: &RistrettoPoint,
        P_point: &RistrettoPoint,
    ) -> Result<(), ProofError> {
        let n = g_vec.len();
        if h_vec.len() != n { return Err(ProofError::InvalidGeneratorsLength); }

        let (s_g, s_h, s_Q_final, s_P, s_U) = self.verification_scalars(n, transcript)?;

        let mut U_points_decompressed: Vec<RistrettoPoint> =
            Vec::with_capacity(self.U_vecs.len() * (2 * self.k - 2));

        for r in 0..self.U_vecs.len() {
            for i_list in 0..(2 * self.k - 2) {
                let U_ir_point = self.U_vecs[r][i_list]
                    .decompress()
                    .ok_or(ProofError::VerificationError)?;
                U_points_decompressed.push(U_ir_point);
            }
        }

        let scalars = s_g.iter().cloned()
            .chain(s_h.iter().cloned())
            .chain(iter::once(s_Q_final))
            .chain(iter::once(-s_P)) 
            .chain(s_U.iter().map(|s| -s)); 

        let points = g_vec.iter()
            .chain(h_vec.iter())
            .chain(iter::once(Q_point))
            .chain(iter::once(P_point))
            .chain(U_points_decompressed.iter());

        let check = RistrettoPoint::vartime_multiscalar_mul(scalars, points);

        if check.is_identity() { Ok(()) } else { Err(ProofError::VerificationError) }
    }
    
    pub fn serialized_size(&self) -> usize {
        let d = self.U_vecs.len();
        let num_points = if d > 0 { d * (2 * self.k - 2) } else { 0 };
        let m = self.a_final.len();
        (3 + num_points + 2 * m) * 32
    }
    
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        let mut temp = [0u8; 32];
        temp[..8].copy_from_slice(&(self.k as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let d = self.U_vecs.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(d as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let m = self.a_final.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(m as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        for round_vec in self.U_vecs.iter() {
            for point in round_vec.iter() { buf.extend_from_slice(point.as_bytes()); }
        }
        for x in &self.a_final { buf.extend_from_slice(x.as_bytes()); }
        for x in &self.b_final { buf.extend_from_slice(x.as_bytes()); }
        buf
    }
    
    pub fn from_bytes(slice: &[u8]) -> Result<K_BulletProof, ProofError> {
        let b = slice.len();
        if b < 32 * 3 { return Err(ProofError::FormatError); }
        use util::read32; 
        let mut pos = 0;

        let k_bytes = read32(&slice[pos..]);
        let k = u64::from_le_bytes(k_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let d_bytes = read32(&slice[pos..]);
        let d = u64::from_le_bytes(d_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;
        let m_bytes = read32(&slice[pos..]);
        let m = u64::from_le_bytes(m_bytes[..8].try_into().unwrap()) as usize;
        pos += 32;

        let points_per_round = 2 * k - 2;
        let mut U_vecs = Vec::with_capacity(d);
        for _ in 0..d {
            let mut round = Vec::with_capacity(points_per_round);
            for _ in 0..points_per_round {
                if pos + 32 > b { return Err(ProofError::FormatError); }
                round.push(CompressedRistretto(read32(&slice[pos..])));
                pos += 32;
            }
            U_vecs.push(round);
        }

        let mut a_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 32 > b { return Err(ProofError::FormatError); }
            let s = Scalar::from_canonical_bytes(read32(&slice[pos..])).ok_or(ProofError::FormatError)?;
            a_final.push(s);
            pos += 32;
        }

        let mut b_final = Vec::with_capacity(m);
        for _ in 0..m {
            if pos + 32 > b { return Err(ProofError::FormatError); }
            let s = Scalar::from_canonical_bytes(read32(&slice[pos..])).ok_or(ProofError::FormatError)?;
            b_final.push(s);
            pos += 32;
        }
        
        Ok(K_BulletProof { k, U_vecs, a_final, b_final })
    }
}


// =========================================================================
//  batched_eCP (eCP with Iterative Padding)
// =========================================================================

#[derive(Clone, Debug)]
pub struct batched_eCP {
    pub(crate) k: usize,
    pub(crate) A_vecs: Vec<Vec<[CompressedRistretto; 2]>>,
    pub(crate) z: Vec<Scalar>, 
}

impl batched_eCP {
    pub fn create(
        transcript: &mut Transcript,
        k: usize, 
        G_vec: &[RistrettoPoint], 
        C1_vec: &[RistrettoPoint], 
        a_vec: &[Scalar],          
        num_rounds: usize, 
    ) -> batched_eCP {
        let n = a_vec.len();
        
        let mut a_curr = a_vec.to_vec();
        let mut G_curr = G_vec.to_vec();
        let mut C1_curr = C1_vec.to_vec();

        if C1_curr.len() < n {
            C1_curr.resize(n, RistrettoPoint::default());
        }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut A_vecs: Vec<Vec<[CompressedRistretto; 2]>> = Vec::with_capacity(num_rounds);

        let mut scalars_0: Vec<Scalar> = Vec::with_capacity(n);
        let mut points_0: Vec<RistrettoPoint> = Vec::with_capacity(n);
        let mut scalars_1: Vec<Scalar> = Vec::with_capacity(n);
        let mut points_1: Vec<RistrettoPoint> = Vec::with_capacity(n);
        
        let mut n_j = n;
        
        for round_idx in 0..num_rounds {
            let rem = n_j % k;
            if rem != 0 {
                let pad = k - rem;
                a_curr.extend(iter::repeat(Scalar::zero()).take(pad));
                G_curr.extend(iter::repeat(RistrettoPoint::default()).take(pad));
                C1_curr.extend(iter::repeat(RistrettoPoint::default()).take(pad));
                n_j += pad;
            }

            let m_j = n_j / k; 
            
            let a_splits: Vec<&[Scalar]> = a_curr.chunks(m_j).collect();
            let G_splits: Vec<&[RistrettoPoint]> = G_curr.chunks(m_j).collect();
            let C1_splits: Vec<&[RistrettoPoint]> = C1_curr.chunks(m_j).collect();
            
            let mut A_vecs_round: Vec<[CompressedRistretto; 2]> = Vec::with_capacity(2 * k - 2);
            let mut A_points_round: Vec<[RistrettoPoint; 2]> = Vec::with_capacity(2 * k - 2);

             for i in 1..k {
                scalars_0.clear(); points_0.clear();
                scalars_1.clear(); points_1.clear();
                for l in 1..(i + 1) {
                    scalars_0.extend_from_slice(a_splits[l - 1]);
                    points_0.extend_from_slice(G_splits[k - i + l - 1]); 
                    scalars_1.extend_from_slice(a_splits[l - 1]);
                    points_1.extend_from_slice(C1_splits[k - i + l - 1]); 
                }
                A_points_round.push([
                    RistrettoPoint::vartime_multiscalar_mul(scalars_0.iter(), points_0.iter()),
                    RistrettoPoint::vartime_multiscalar_mul(scalars_1.iter(), points_1.iter()),
                ]);
            }
            for i in 1..k {
                scalars_0.clear(); points_0.clear();
                scalars_1.clear(); points_1.clear();
                for l in 1..(k - i + 1) {
                    scalars_0.extend_from_slice(a_splits[i + l - 1]);
                    points_0.extend_from_slice(G_splits[l - 1]); 
                    scalars_1.extend_from_slice(a_splits[i + l - 1]);
                    points_1.extend_from_slice(C1_splits[l - 1]); 
                }
                A_points_round.push([
                    RistrettoPoint::vartime_multiscalar_mul(scalars_0.iter(), points_0.iter()),
                    RistrettoPoint::vartime_multiscalar_mul(scalars_1.iter(), points_1.iter()),
                ]);
            }

            for (idx, points_tuple) in A_points_round.iter().enumerate() {
                 let compressed_tuple = [ points_tuple[0].compress(), points_tuple[1].compress() ];
                 A_vecs_round.push(compressed_tuple);
                 
                 transcript.append_message(b"A_round", &(round_idx as u64).to_le_bytes());
                 transcript.append_message(b"A_index", &(idx as u64).to_le_bytes());
                 transcript.commit_point(b"A_point_0", &compressed_tuple[0]);
                 transcript.commit_point(b"A_point_1", &compressed_tuple[1]);
            }
            A_vecs.push(A_vecs_round);

            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(round_idx as u64).to_le_bytes());
            let c = transcript.challenge_scalar(b"challenge_separator");
            
            let mut a_new = vec![Scalar::zero(); m_j];
            let mut G_new = vec![RistrettoPoint::default(); m_j];
            let mut C1_new = vec![RistrettoPoint::default(); m_j];

            let mut c_powers_a: Vec<Scalar> = Vec::with_capacity(k);
            let mut c_pow = Scalar::one();
            for _ in 0..k { c_powers_a.push(c_pow); c_pow *= c; }

            for j_item in 0..m_j {
                let mut a_acc = Scalar::zero();
                for i in 0..k { a_acc += a_splits[i][j_item] * c_powers_a[i]; }
                a_new[j_item] = a_acc;
            }

            let c_inv = c.invert();
            let mut c_powers_bases = Vec::with_capacity(k);
            let mut c_pow_exp = scalar_pow(c, k as u64); 
            for _ in 0..k { c_powers_bases.push(c_pow_exp); c_pow_exp *= c_inv; }

            let mut g_col = vec![RistrettoPoint::default(); k];
            let mut c1_col = vec![RistrettoPoint::default(); k];

            for j_item in 0..m_j {
                for i in 0..k {
                    g_col[i] = G_splits[i][j_item];
                    c1_col[i] = C1_splits[i][j_item];
                }
                G_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(c_powers_bases.iter(), g_col.iter());
                C1_new[j_item] = RistrettoPoint::vartime_multiscalar_mul(c_powers_bases.iter(), c1_col.iter());
            }

            a_curr = a_new;
            G_curr = G_new;
            C1_curr = C1_new;
            n_j = m_j;
        }

        batched_eCP {
            k,
            A_vecs,
            z: a_curr,
        }
    }

    pub fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<Scalar>, Scalar, Vec<Scalar>), ProofError> {
        let k = self.k;
        let d = self.A_vecs.len();

        let round_lengths = reconstruct_round_lengths(n, k, d);
        let m = *round_lengths.last().unwrap();

        if self.z.len() != m { return Err(ProofError::VerificationError); }

        transcript.append_message(b"protocol-name", b"k_ipp_delay_2");
        transcript.append_message(b"n", &(n as u64).to_le_bytes());
        transcript.append_message(b"k", &(k as u64).to_le_bytes());

        let mut challenges: Vec<Scalar> = Vec::with_capacity(d);
        for r in 0..d { 
            for i_list in 0..(2 * k - 2) {
                let tuple = self.A_vecs[r][i_list];
                transcript.append_message(b"A_round", &(r as u64).to_le_bytes());
                transcript.append_message(b"A_index", &(i_list as u64).to_le_bytes());
                transcript.commit_point(b"A_point_0", &tuple[0]);
                transcript.commit_point(b"A_point_1", &tuple[1]);
            }
            transcript.append_message(b"challenge_prefix", b"c_");
            transcript.append_message(b"challenge_index", &(r as u64).to_le_bytes());
            challenges.push(transcript.challenge_scalar(b"challenge_separator"));
        }

        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);

        let mut s_P = Scalar::one();
        let k_exp = k as u64;
        let mut c_k_products = vec![Scalar::one(); d]; 
        let mut product_so_far = Scalar::one();
        for r in (0..d).rev() {
            let c_k = scalar_pow(challenges[r], k_exp);
            c_k_products[r] = product_so_far;
            product_so_far *= c_k;
        }
        s_P = product_so_far; 

        let mut z_s_vec = self.z.clone();
        for r in (0..d).rev() {
            let c_inv = challenges_inv[r];
            let mut block = Vec::with_capacity(k);
            let mut val = Scalar::one();
            for _ in 0..k { block.push(val); val *= c_inv; }

            let mut next_s = Vec::with_capacity(z_s_vec.len() * k);
            for b in block.iter() {
                for z_val in z_s_vec.iter() { next_s.push(z_val * b); }
            }
            
            next_s.truncate(round_lengths[r]);
            z_s_vec = next_s;
        }

        for x in z_s_vec.iter_mut() {
            *x *= s_P;
        }

        let mut s_A_vec: Vec<Scalar> = Vec::with_capacity(d * (2*k-2));
        for r in 0..d { 
            let c_r = challenges[r];
            let suffix_prod = c_k_products[r]; 
            for i in 1..k { 
                s_A_vec.push(scalar_pow(c_r, i as u64) * suffix_prod);
            }
            for i in 1..k { 
                s_A_vec.push(scalar_pow(c_r, (k + i) as u64) * suffix_prod);
            }
        }
        
        Ok((z_s_vec, s_P, s_A_vec))
    }
    
    #[allow(dead_code)]
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        G_vec: &Vec<RistrettoPoint>,
        C1_vec: &Vec<RistrettoPoint>,
        P0: &RistrettoPoint,
        P1: &RistrettoPoint,
    ) -> Result<(), ProofError> {
        let n = G_vec.len();
        let (z_s_vec, s_P, s_A_vec) =
            self.verification_scalars(n, transcript).map_err(|_| ProofError::VerificationError)?;

        let r1 = transcript.challenge_scalar(b"r1");

        let mut A_points_combined: Vec<RistrettoPoint> =
            Vec::with_capacity(self.A_vecs.len() * (2 * self.k - 2));

        for r in 0..self.A_vecs.len() {
            for i_list in 0..(2 * self.k - 2) {
                let A_0 = self.A_vecs[r][i_list][0].decompress().ok_or(ProofError::VerificationError)?;
                let A_1 = self.A_vecs[r][i_list][1].decompress().ok_or(ProofError::VerificationError)?;
                A_points_combined.push(A_0 + r1 * A_1);
            }
        }
        
        let z_s_r1: Vec<Scalar> = z_s_vec.iter().map(|s| s * r1).collect();
        let P_comb = P0 + r1 * P1;

        let scalars = z_s_vec.iter().cloned()
            .chain(z_s_r1.into_iter())
            .chain(iter::once(-s_P))
            .chain(s_A_vec.iter().map(|s| -s));

        let points = G_vec.iter()
            .chain(C1_vec.iter())
            .chain(iter::once(&P_comb))
            .chain(A_points_combined.iter());
        
        let check = RistrettoPoint::vartime_multiscalar_mul(scalars, points);

        if check.is_identity() { Ok(()) } else { Err(ProofError::VerificationError) }
    }

    pub fn serialized_size(&self) -> usize {
        let d = self.A_vecs.len();
        let mut num_points = 0;
        if d > 0 {
            num_points = d * (2 * self.k - 2) * 2;
        }
        let m = self.z.len();
        (3 + num_points + m) * 32
    }
    
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        let mut temp = [0u8; 32];
        temp[..8].copy_from_slice(&(self.k as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let d = self.A_vecs.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(d as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        let m = self.z.len();
        temp = [0u8; 32];
        temp[..8].copy_from_slice(&(m as u64).to_le_bytes());
        buf.extend_from_slice(&temp);

        for round_vec in self.A_vecs.iter() {
            for point_tuple in round_vec.iter() {
                buf.extend_from_slice(point_tuple[0].as_bytes());
                buf.extend_from_slice(point_tuple[1].as_bytes());
            }
        }
        for s in &self.z { buf.extend_from_slice(s.as_bytes()); }
        buf
    }

    pub fn from_bytes(slice: &[u8]) -> Result<batched_eCP, ProofError> {
         let b = slice.len();
         if b < 32 * 3 { return Err(ProofError::FormatError); }
         use util::read32; 
         let mut pos = 0;
         let k_bytes = read32(&slice[pos..]);
         let k = u64::from_le_bytes(k_bytes[..8].try_into().unwrap()) as usize;
         pos += 32;
         let d_bytes = read32(&slice[pos..]);
         let d = u64::from_le_bytes(d_bytes[..8].try_into().unwrap()) as usize;
         pos += 32;
         let m_bytes = read32(&slice[pos..]);
         let m = u64::from_le_bytes(m_bytes[..8].try_into().unwrap()) as usize;
         pos += 32;

         let mut A_vecs = Vec::with_capacity(d);
         for _ in 0..d {
             let mut round = Vec::with_capacity(2 * k - 2);
             for _ in 0..(2 * k - 2) {
                 if pos + 64 > b { return Err(ProofError::FormatError); }
                 let p0 = CompressedRistretto(read32(&slice[pos..]));
                 pos += 32;
                 let p1 = CompressedRistretto(read32(&slice[pos..]));
                 pos += 32;
                 round.push([p0, p1]);
             }
             A_vecs.push(round);
         }
         let mut z = Vec::with_capacity(m);
         for _ in 0..m {
             if pos + 32 > b { return Err(ProofError::FormatError); }
             let s = Scalar::from_canonical_bytes(read32(&slice[pos..])).ok_or(ProofError::FormatError)?;
             z.push(s);
             pos += 32;
         }
         Ok(batched_eCP { k, A_vecs, z })
    }
}

pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    let mut out = Scalar::zero();
    if a.len() != b.len() { panic!("inner_product(a,b): lengths of vectors do not match"); }
    for i in 0..a.len() { out += a[i] * b[i]; }
    out
}
    
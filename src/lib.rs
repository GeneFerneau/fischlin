#![no_std]

use secp256k1::bitcoin_hashes::{sha256, Hash, HashEngine};
use secp256k1::{Error as SecpError, PublicKey, Secp256k1, SecretKey, Signing, Verification};

/// Bit-size of the witness
const K: usize = 256;

/// Bit-size of the challenge hash function (lower bits of the hash digest)
///
/// log2(K) * 2
const B: usize = K / 16;

/// Number of repetitions for computing challenges and responses
///
/// log2(K) * 2
pub const R: usize = K / 16;

/// Maximum sum of the challenge hashes
const S: u16 = R as u16;

/// Bit-size of the challenges
///
/// log2(K) * 3
const T: usize = K / 16 + 8;

/// Error types for Fischlin proofs
#[derive(Debug)]
pub enum Error {
    InvalidProof,
}

/// Commitment to randomness used in the proof of knowledge 
#[derive(Copy, Clone, PartialEq)]
pub struct Commitment([u8; 33]);

impl Commitment {
    pub fn new() -> Self {
        Self([1u8; 33])
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl From<&PublicKey> for Commitment {
    fn from(k: &PublicKey) -> Self {
        Self(k.serialize())
    }
}

impl From<PublicKey> for Commitment {
    fn from(k: PublicKey) -> Self {
        Self(k.serialize())
    }
}

impl Default for Commitment {
    fn default() -> Self {
        Self::new()
    }
}

/// Challenge submitted to the prover (T-bits)
#[derive(Copy, Clone, PartialEq)]
pub struct Challenge(u32);

impl Challenge {
    pub fn new() -> Self {
        Self(1)
    }

    pub fn as_bytes(&self) -> [u8; 4] {
        self.0.to_be_bytes()
    }
}

impl From<u32> for Challenge {
    fn from(t: u32) -> Self {
        if t == 0 || t & 0xffu32 << T != 0 {
            panic!("invalid value for the challenge: {}, range: 1..{}", t, (1u32 << T) - 1);
        }
        Self(t)
    }
}

impl Default for Challenge {
    fn default() -> Self {
        Self::new()
    }
}

/// Response from queries to the prover
#[derive(Copy, Clone, PartialEq)]
pub struct Response([u8; 32]);

impl Response {
    pub fn new() -> Self {
        Self([1u8; 32])
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl From<&SecretKey> for Response {
    fn from(k: &SecretKey) -> Self {
        Self(k.as_ref().clone())
    }
}

impl From<SecretKey> for Response {
    fn from(k: SecretKey) -> Self {
        Self(k.as_ref().clone())
    }
}

impl Default for Response {
    fn default() -> Self {
        Self::new()
    }
}

/// Proof of knowledge of exponent
#[derive(Copy, Clone, PartialEq)]
pub struct Proof([(Commitment, Challenge, Response); R]);

impl Proof {
    /// Create a new proof with default partial proofs
    pub fn new() -> Self {
        Self([(Commitment::default(), Challenge::default(), Response::default()); R])
    }

    /// Get a reference to the collection of partial proofs
    pub fn inner(&self) -> &[(Commitment, Challenge, Response); R] {
        &self.0
    }

    /// Get a mutable reference to the collection of partial proofs
    pub fn inner_mut(&mut self) -> &mut [(Commitment, Challenge, Response); R] {
        &mut self.0
    }
}


impl From<[(Commitment, Challenge, Response); R]> for Proof {
    fn from(p: [(Commitment, Challenge, Response); R]) -> Self {
        Self(p)
    }
}

impl Default for Proof {
    fn default() -> Self {
        Self::new()
    }
}

/// Prove knowledge of exponent using Fischlin NIZK proofs
///
/// Computes `R` challenge-response pairs over Schnorr proofs of identity
/// by submitting `1, 2, 3, ..., 2^T - 1` as `T`-bit string challenges.
///
/// The witness, commitment vector, index, challenge, and response are
/// input into a hash function (SHA-256), and the first B bits are checked
/// to be equal to zero.
///
/// If the bits are zero, the tuple (commitment, challenge, response) is accepted as
/// a partial proof. If not, the challenge with the lowest value (`B` bits interpreted
/// as a big-endian integer) without causing the cumulative sum to go over `S` is accepted.
/// 
/// If no valid challenges are found for any given commitment, the proof is invalid, and must
/// be retried with new randomness for the commitments (extremely unlikely).
///
/// Example:
///
/// ```rust-no-run
///    # extern crate alloc;
///
///    # use alloc::vec::Vec;
///
///    # use fischlin::prove;
///    # use rand::rngs::OsRng;
///    # use rand::RngCore;
///    # use secp256k1::{Secp256k1, SecretKey};
///    # use secp256k1_sys::types::AlignedType;
///
///    let mut w_bytes = [0u8; 32];
///    OsRng.fill_bytes(&mut w_bytes);
///    let w = SecretKey::from_slice(&w_bytes).unwrap();
///
///    let mut vs = [secp256k1::key::ONE_KEY; R];
///    for v in vs.iter_mut() {
///        let mut v_bytes = [0u8; 32];
///        OsRng.fill_bytes(&mut v_bytes);
///        *v = SecretKey::from_slice(&v_bytes).unwrap();
///    }
///
///    let secp_size = Secp256k1::preallocate_size();
///    let mut secp_buf: Vec<AlignedType> = Vec::with_capacity(secp_size);
///    secp_buf.resize(secp_size, AlignedType::default());
///    let secp = Secp256k1::preallocated_new(&mut secp_buf[..]).unwrap();
///
///    let _proofs = prove(&secp, &w, &vs).unwrap();
/// ```
pub fn prove<C: Signing + Verification>(
    secp: &Secp256k1<C>,
    w: &SecretKey,
    vs: &[SecretKey; R],
) -> Result<Proof, Error> {
    let x = PublicKey::from_secret_key(secp, w);
    let mut engine = sha256::Hash::engine();
    engine.input(&x.serialize());

    let mut coms = [Commitment::default(); R];
    for (i, v) in vs.iter().enumerate() {
        coms[i] = PublicKey::from_secret_key(secp, v).into();
        engine.input(coms[i].as_bytes());
    }

    let mut proof = Proof::new();
    let proofs = proof.inner_mut();
    let mut sum = 0u16;
    for (i, v) in vs.iter().enumerate() {
        // clone the hash engine to not have to recompute constant terms
        let mut prove_engine = engine.clone();
        prove_engine.input(&(i as u16).to_be_bytes());

        let mut min_attempt: Option<(Challenge, Response, u16)> = None;
        'outer: for t in 0..T {
            let beg_chal: u32 = 1u32 << t;
            let end_chal: u32 = 1u32 << t + 1;

            for chal in beg_chal..end_chal {
                let chal = Challenge(chal);
                // get the Schnorr proof response for the witness, current randomness, and challenge
                let resp = schnorr_prove(w, v, &chal).map_err(|_| Error::InvalidProof)?;

                let mut t_engine = prove_engine.clone();
                // add the challenge to the hash
                t_engine.input(&chal.as_bytes()[1..]);
                // add the response to the hash
                t_engine.input(resp.as_bytes());

                // calculate the score as the first B-bits of the hash
                let hash = sha256::Hash::from_engine(t_engine);
                let mut hash_slice = [0; 2];
                hash_slice.copy_from_slice(&hash.into_inner()[..B/8]);
                let score = u16::from_be_bytes(hash_slice);

                if score == 0 {
                    // score is zero, found valid partial proof
                    // add to proofs, and move on to next commitment
                    proofs[i] = (coms[i], chal, resp);
                    break 'outer;
                } else if let Some(attempt) = min_attempt {
                    let (_, _, att_score) = attempt;
                    if score < att_score && sum.saturating_add(score) <= S {
                        // found a potentially valid minimum proof, set as new minimum
                        min_attempt = Some((chal, resp, score));
                    }
                } else {
                    // no minimum valid attempt found, add one
                    if sum.saturating_add(score) <= S {
                        min_attempt = Some((chal, resp, score));
                    }
                }
            }

            if t == T - 1 {
                match min_attempt {
                    // Add the minimum valid partial proof
                    Some(attempt) => {
                        let (chal, resp, score) = attempt;
                        sum = sum.saturating_add(score);
                        proofs[i] = (coms[i], chal, resp);
                    }
                    // No valid partial proof found for the commitment (extremely unlikely)
                    None => return Err(Error::InvalidProof),
                }
            }
        }
    }

    // completeness check, ensure proof is valid before sending to verifier
    // extremely unlikely to fail
    if verify(secp, &x, &proof)? {
        Ok(proof)
    } else {
        Err(Error::InvalidProof)
    }
}

/// Verify Fischlin NIZK proofs of knowledge of exponent for a discrete logarithm
///
/// For the challenge `x` and proof tuples `(commit, challenge, response)`, verify that each
/// Schnorr proof of identity is valid, and :
/// 
/// > Sum[i=0, R-1](Hash(x, commits, i, challenge[i], response[i])[..HashLen-B]) <= S
///
/// Otherwise, the proof is invalid.
///
/// Example:
///
/// ```rust-no-run
///    # extern crate alloc;
///
///    # use alloc::vec::Vec;
///
///    # use fischlin::{prove, verify};
///    # use rand::rngs::OsRng;
///    # use rand::RngCore;
///    # use secp256k1::{Secp256k1, SecretKey};
///    # use secp256k1_sys::types::AlignedType;
///
///    let mut w_bytes = [0u8; 32];
///    OsRng.fill_bytes(&mut w_bytes);
///    let w = SecretKey::from_slice(&w_bytes).unwrap();
///
///    let mut vs = [secp256k1::key::ONE_KEY; R];
///    for v in vs.iter_mut() {
///        let mut v_bytes = [0u8; 32];
///        OsRng.fill_bytes(&mut v_bytes);
///        *v = SecretKey::from_slice(&v_bytes).unwrap();
///    }
///
///    let secp_size = Secp256k1::preallocate_size();
///    let mut secp_buf: Vec<AlignedType> = Vec::with_capacity(secp_size);
///    secp_buf.resize(secp_size, AlignedType::default());
///    let secp = Secp256k1::preallocated_new(&mut secp_buf[..]).unwrap();
///
///    let proofs = prove(&secp, &w, &vs).unwrap();
///
///    let x = PublicKey::from_secret_key(&secp, &w);
///
///    assert!(verify(&secp, &x, &proofs).unwrap());
/// ```
pub fn verify<C: Signing + Verification>(
    secp: &Secp256k1<C>,
    x: &PublicKey,
    proof: &Proof,
) -> Result<bool, Error> {
    let mut sum = 0u16;
    let mut engine = sha256::Hash::engine();

    engine.input(&x.serialize());

    let proofs = proof.inner();

    for (com, _, _) in proofs.iter() {
        engine.input(com.as_bytes());
    }

    for (i, (com, chal, resp)) in proofs.iter().enumerate() {
        if !schnorr_verify(secp, x, &com, &chal, &resp).map_err(|_| Error::InvalidProof)? {
            return Ok(false);
        }

        // clone the hash engine to not have to recompute constant terms
        let mut mid_engine = engine.clone();
        mid_engine.input(&(i as u16).to_be_bytes());
        mid_engine.input(&chal.as_bytes()[1..]);
        mid_engine.input(resp.as_bytes());

        let hash = sha256::Hash::from_engine(mid_engine);
        let mut hash_slice = [0; 2];
        hash_slice.copy_from_slice(&hash.into_inner()[..B/8]);
        let score = u16::from_be_bytes(hash_slice);

        if sum.saturating_add(score) > S as u16 {
            return Ok(false);
        } else {
            sum = sum.saturating_add(score);
        }
    }

    Ok(true)
}

fn schnorr_prove(w: &SecretKey, v: &SecretKey, t: &Challenge) -> Result<Response, SecpError> {
    let mut r_bytes = [0; 32]; 
    r_bytes[28..].copy_from_slice(&t.as_bytes());
    let mut r = SecretKey::from_slice(&r_bytes)?;

    // r = v - w*t
    r.mul_assign(w.as_ref())?;
    r.negate_assign();
    r.add_assign(v.as_ref())?;

    Ok(r.into())
}

fn schnorr_verify<C: Signing + Verification>(
    secp: &Secp256k1<C>,
    x: &PublicKey,
    com: &Commitment,
    chal: &Challenge,
    resp: &Response,
) -> Result<bool, SecpError> {
    let mut commit = x.clone();
    let mut c_bytes = [0; 32];
    c_bytes[28..].copy_from_slice(&chal.as_bytes());
    let c = SecretKey::from_slice(&c_bytes)?;

    // cX
    commit.mul_assign(secp, c.as_ref())?;
    // rG + cX
    commit.add_exp_assign(secp, resp.as_bytes())?;

    // V = rG + cX
    // non-constant compare is safe, no secret data is being compared
    Ok(com == &commit.into())
}

#[cfg(test)]
mod tests {
    extern crate alloc;

    use alloc::vec::Vec;

    use super::*;
    use rand::rngs::OsRng;
    use rand::RngCore;
    use secp256k1_sys::types::AlignedType;

    #[test]
    fn test_schnorr_prove() {
        let mut w_bytes = [0u8; 32];
        OsRng.fill_bytes(&mut w_bytes);
        let w = SecretKey::from_slice(&w_bytes).unwrap();
        
        OsRng.fill_bytes(&mut w_bytes);
        let v = SecretKey::from_slice(&w_bytes).unwrap();

        for t in 0..T {
            let chal = Challenge(1u32 << t);
            let _proof = schnorr_prove(&w, &v, &chal).unwrap();
        }
    }

    #[test]
    fn test_schnorr_verify() {
        let mut w_bytes = [0u8; 32];
        OsRng.fill_bytes(&mut w_bytes);
        let w = SecretKey::from_slice(&w_bytes).unwrap();
        
        OsRng.fill_bytes(&mut w_bytes);
        let v = SecretKey::from_slice(&w_bytes).unwrap();

        let secp_size = Secp256k1::preallocate_size();
        let mut secp_buf: Vec<AlignedType> = Vec::with_capacity(secp_size);
        secp_buf.resize(secp_size, AlignedType::default());

        let secp = Secp256k1::preallocated_new(&mut secp_buf[..]).unwrap();

        let x = PublicKey::from_secret_key(&secp, &w);
        let com = PublicKey::from_secret_key(&secp, &v).into();

        for t in 0..T {
            let chal = Challenge(1u32 << t);
            let response = schnorr_prove(&w, &v, &chal).unwrap();

            assert!(schnorr_verify(&secp, &x, &com, &chal, &response).unwrap());
        }
    }

    #[test]
    fn test_prove_verify() {
        let mut w_bytes = [0u8; 32];
        OsRng.fill_bytes(&mut w_bytes);
        let w = SecretKey::from_slice(&w_bytes).unwrap();

        let mut vs = [secp256k1::key::ONE_KEY; R];
        for v in vs.iter_mut() {
            let mut v_bytes = [0u8; 32];
            OsRng.fill_bytes(&mut v_bytes);
            *v = SecretKey::from_slice(&v_bytes).unwrap();
        }

        let secp_size = Secp256k1::preallocate_size();
        let mut secp_buf: Vec<AlignedType> = Vec::with_capacity(secp_size);
        secp_buf.resize(secp_size, AlignedType::default());
        let secp = Secp256k1::preallocated_new(&mut secp_buf[..]).unwrap();

        let proofs = prove(&secp, &w, &vs).unwrap();

        let x = PublicKey::from_secret_key(&secp, &w);

        assert!(verify(&secp, &x, &proofs).unwrap());
    }
}

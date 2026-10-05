//! Standalone Winternitz One-Time Signature (WOTS) over Poseidon2/BabyBear,
//! using a **target-sum** message encoding instead of a classical WOTS+
//! checksum chain.
//!
//! # Why target-sum instead of a checksum
//!
//! Classical WOTS+ (RFC 8391) appends extra "checksum" chains so a forger
//! can't trade "some digits lower" for "other digits higher" (chains can
//! only be walked forward). Target-sum Winternitz gets the same guarantee a
//! different way: the signer encodes the message together with a public
//! randomizer, and retries with a fresh randomizer until the resulting digit
//! vector sums to an exact, fixed target `T`. The verifier recomputes the
//! same digits from (message, randomizer), so the sum constraint is checked
//! for free -- no separate checksum chains, and critically, a *fixed* number
//! of chain-hash calls per verification regardless of the message. That
//! fixed-cost property is exactly what you want for a hash-chain
//! verification you intend to arithmetize into a STARK AIR: no branches, no
//! data-dependent circuit size.
//!
//! This is the approach taken by Khovratovich, Kudinov, and Wagner,
//! "Hash-Based Multi-Signatures for Post-Quantum Ethereum" (CRYPTO 2025),
//! and instantiated over Poseidon2/BabyBear/KoalaBear by Drake, "Technical
//! Note: LeanSig for Post-Quantum Ethereum" (IACR eprint 2025/1332), which
//! this module follows for its hash-call shapes (`PoseidonCompress`, see
//! `poseidon2::Poseidon2BabyBear::compress`) and its "Hashing-Optimized"
//! chain-count/base choice (v=64, w=8), picked here because minimizing the
//! *number* of hash calls during verification is what matters when that
//! verification will be expressed as a STARK circuit.
//!
//! One deliberate deviation from the paper's own numbers: they set `T = 375`,
//! reachable in their scheme only because `MapToVertex` *constructs* a digit
//! vector directly inside a chosen top layer of the hypercube, rather than
//! finding one by chance. This module derives digits by hashing and reducing
//! mod `W` (see "What's deliberately simplified" below), which samples
//! uniformly over the *whole* hypercube -- so `T` has to be reachable by
//! rejection sampling. `T = 375` is about 8 standard deviations above that
//! distribution's mean and would need on the order of 10^16 attempts. This
//! module instead targets `T = V * (W - 1) / 2 = 224`, the hypercube's
//! central (most probable) layer, where a valid randomizer turns up in a
//! handful of trials. Incomparability -- the property target-sum encodings
//! actually need for security -- holds for *any* fixed-sum layer, not only
//! near-maximal ones, so this is still a faithful target-sum-Winternitz
//! instantiation at the same (v, w) as the paper's preset, just with a
//! target sum suited to this module's simpler digit derivation.
//!
//! # What's deliberately simplified vs. the paper
//!
//! This is a **standalone** one-time signature: no Merkle-tree aggregation
//! of many WOTS keys, no "epoch"/lifetime handling, and no "top layer
//! hypercube" optimization (that trick only pays off when amortized across
//! many signatures in a tree, which is future work per the project plan).
//! The digit-vector derivation here is also a simpler (but functionally
//! equivalent) rejection-sampling scheme over the full hypercube rather than
//! the paper's exact bijective `MapToVertex` encoding -- this is *not*
//! meant to be bit-compatible with LeanSig, just a faithful, from-scratch
//! implementation of the same target-sum-Winternitz security idea, built on
//! our own verified Poseidon2 permutation.

// `main.rs` doesn't call into this module yet (it just prints "Hello
// world!"), so allow dead code here rather than suppressing warnings
// piecemeal -- this module exists to be exercised by its tests for now.
#![allow(dead_code)]

use crate::poseidon2::{BabyBear, Poseidon2BabyBear};

/// Winternitz base: each chain digit is in `0..W`.
pub const W: u32 = 8;
/// Number of hash chains (the "Hashing-Optimized" LeanSig preset).
pub const V: usize = 64;
/// Maximum steps per chain.
pub(crate) const CHAIN_STEPS: u32 = W - 1;
/// Fixed digit-sum every valid signature's encoding must hit exactly: the
/// hypercube's central layer (see module docs for why this differs from
/// the paper's `T = 375`).
pub const TARGET_SUM: u32 = (V as u32) * (W - 1) / 2;
/// Give up after this many rejection-sampling attempts (matches the paper's
/// default trial cap `K = 2^12`; the expected number of attempts needed for
/// this preset is small -- tens, not thousands).
const MAX_TRIALS: u32 = 1 << 12;

pub(crate) const PARAM_LEN: usize = 5;
pub(crate) const CHAIN_LEN: usize = 8;
pub(crate) const RAND_LEN: usize = 7;
const SEED_LEN: usize = 8;

pub(crate) type Param = [BabyBear; PARAM_LEN];
pub(crate) type ChainValue = [BabyBear; CHAIN_LEN];

/// Domain-separation tags: distinguish the different *purposes* a hash call
/// serves (deriving the public parameter, deriving secret chains, hashing a
/// chain step, hashing a message) so that no two purposes can ever collide
/// on the same input, even accidentally.
const TAG_PARAM: u32 = 1;
const TAG_SECRET: u32 = 2;
pub(crate) const TAG_CHAIN: u32 = 3;
pub(crate) const TAG_MESSAGE: u32 = 4;

pub struct SecretKey {
    param: Param,
    chains: [ChainValue; V],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub param: Param,
    pub tops: [ChainValue; V],
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub randomizer: [BabyBear; RAND_LEN],
    pub values: [ChainValue; V],
}

/// Little-endian-encode a sequence of field elements, 4 bytes each.
fn encode_elements<'a>(elems: impl IntoIterator<Item = &'a BabyBear>) -> Vec<u8> {
    let mut out = Vec::new();
    for e in elems {
        out.extend_from_slice(&e.to_bytes());
    }
    out
}

/// Decode exactly `count` field elements (4 bytes each) from `bytes`,
/// returning `None` if the length doesn't match.
fn decode_elements(bytes: &[u8], count: usize) -> Option<Vec<BabyBear>> {
    if bytes.len() != count * 4 {
        return None;
    }
    Some(
        bytes
            .chunks_exact(4)
            .map(|c| BabyBear::from_bytes(c.try_into().unwrap()))
            .collect(),
    )
}

/// Exact byte length of `PublicKey::to_bytes()` -- fixed at compile time
/// (`PARAM_LEN` and `V` are both constants), so any caller needing to
/// chunk a buffer of concatenated public keys can rely on this rather
/// than re-deriving the arithmetic.
pub const PUBLIC_KEY_LEN: usize = (PARAM_LEN + V * CHAIN_LEN) * 4;

/// A signature's encoded length: the randomizer, then a value per chain.
pub const SIGNATURE_LEN: usize = (RAND_LEN + V * CHAIN_LEN) * 4;

impl PublicKey {
    /// Every field element of the key, in order: `param`, then `tops`
    /// chain by chain.
    pub fn elements(&self) -> Vec<BabyBear> {
        self.param.iter().chain(self.tops.iter().flatten()).copied().collect()
    }

    /// The key's hash -- what an output records as its owner. Over the
    /// key's field elements directly (`hash_elements`), so a block's proof
    /// can recompute it without unpacking bytes: `param` zero-padded to 8
    /// elements, then the 64 tops. The padding lines every top up with a
    /// half of one of the sponge's 16-element absorption blocks -- block 0
    /// takes `param` and top 0, block `k` tops `2k - 1` and `2k`, and the
    /// last top 63 alone -- so the circuit can absorb each top straight
    /// from the chain that produced it.
    pub fn hash(&self) -> [BabyBear; 8] {
        crate::poseidon2::hash_elements(crate::poseidon2::DOMAIN_PUBKEY, &self.hash_input())
    }

    /// Exactly what `hash` absorbs.
    pub fn hash_input(&self) -> Vec<BabyBear> {
        let mut out = self.param.to_vec();
        out.resize(CHAIN_LEN, BabyBear::ZERO);
        out.extend(self.tops.iter().flatten());
        out
    }

    /// Serialize to little-endian bytes: `param` (5 elements) followed by
    /// `tops` (`V` chains of 8 elements each), 4 bytes per element. This is
    /// the format a real verifier -- a separate process with no access to
    /// the signer's memory -- would actually receive.
    pub fn to_bytes(&self) -> Vec<u8> {
        encode_elements(self.param.iter().chain(self.tops.iter().flatten()))
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let elems = decode_elements(bytes, PARAM_LEN + V * CHAIN_LEN)?;
        let mut it = elems.into_iter();
        let param: Param = std::array::from_fn(|_| it.next().unwrap());
        let tops: [ChainValue; V] =
            std::array::from_fn(|_| std::array::from_fn(|_| it.next().unwrap()));
        Some(PublicKey { param, tops })
    }
}

impl Signature {
    /// Serialize to little-endian bytes: `randomizer` (7 elements) followed
    /// by `values` (`V` chains of 8 elements each), 4 bytes per element.
    pub fn to_bytes(&self) -> Vec<u8> {
        encode_elements(self.randomizer.iter().chain(self.values.iter().flatten()))
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let elems = decode_elements(bytes, RAND_LEN + V * CHAIN_LEN)?;
        let mut it = elems.into_iter();
        let randomizer: [BabyBear; RAND_LEN] = std::array::from_fn(|_| it.next().unwrap());
        let values: [ChainValue; V] =
            std::array::from_fn(|_| std::array::from_fn(|_| it.next().unwrap()));
        Some(Signature { randomizer, values })
    }
}

/// Convert a byte seed into exactly `SEED_LEN` field elements (4 bytes -> one
/// element each, little-endian, reduced mod P). The seed is not hashed first,
/// so a 32-byte seed maps directly and deterministically onto the 8 elements
/// used below; use a full-entropy, never-reused seed per keypair, as with
/// any one-time signature scheme.
fn seed_to_elements(seed: &[u8; 32]) -> [BabyBear; SEED_LEN] {
    let mut out = [BabyBear::ZERO; SEED_LEN];
    for (i, chunk) in seed.chunks_exact(4).enumerate() {
        let bytes: [u8; 4] = chunk.try_into().unwrap();
        out[i] = BabyBear::new(u32::from_le_bytes(bytes));
    }
    out
}

/// Hash an arbitrary-length message down to the fixed 8-element digest WOTS
/// signs. This is purely a convenience for turning real messages into the
/// fixed-size digest `sign`/`verify` expect; any hash of equivalent strength
/// would do just as well.
pub fn hash_message(message: &[u8]) -> [BabyBear; 8] {
    crate::poseidon2::hash_bytes(message)
}

/// One step of a hash chain: `PoseidonCompress_{24,8}(param, tag,
/// chain_index, step_index, value, 0...)`. Domain-separated by chain index
/// and step index so that no two (chain, step) positions, across any key,
/// ever hash the same input unless the value does too.
///
/// Width 24 rather than the 16 these 16 input elements would fit: chain
/// steps are nearly all of what a block's proof computes, and every other
/// hash in that proof is width 24 -- one permutation circuit for all of
/// them, rather than two plus a switch between them, roughly halves the
/// proof's cost.
pub(crate) fn chain_step(
    perm24: &Poseidon2BabyBear<24>,
    param: &Param,
    chain_index: usize,
    step_index: u32,
    value: ChainValue,
) -> ChainValue {
    let mut input = [BabyBear::ZERO; 24];
    input[0..PARAM_LEN].copy_from_slice(param);
    input[5] = BabyBear::new(TAG_CHAIN);
    input[6] = BabyBear::new(chain_index as u32);
    input[7] = BabyBear::new(step_index);
    input[8..16].copy_from_slice(&value);
    perm24.compress::<CHAIN_LEN>(input)
}

/// Derive the target-sum digit vector for (param, message_digest,
/// randomizer): `PoseidonCompress_{24,8}` produces 8 field elements, each
/// decomposed into 10 base-`W` digits (3 bits each, well inside an element's
/// ~31 bits, so the bias from the implicit mod-W reduction is negligible --
/// around 2^-28). The first `V` of the resulting ~80 digits become the
/// signature's digit vector.
pub(crate) fn derive_digits(
    param: &Param,
    message_digest: [BabyBear; 8],
    randomizer: [BabyBear; RAND_LEN],
) -> [u32; V] {
    let perm24 = crate::poseidon2::perm24();
    let mut input = [BabyBear::ZERO; 24];
    input[0..PARAM_LEN].copy_from_slice(param);
    input[5] = BabyBear::new(TAG_MESSAGE);
    input[6..14].copy_from_slice(&message_digest);
    input[14..21].copy_from_slice(&randomizer);
    let out: [BabyBear; 8] = perm24.compress(input);

    let mut digits = [0u32; V];
    let mut idx = 0;
    'outer: for elem in out {
        let mut v = elem.value();
        for _ in 0..10 {
            if idx == V {
                break 'outer;
            }
            digits[idx] = v % W;
            v /= W;
            idx += 1;
        }
    }
    debug_assert_eq!(idx, V, "W and the 8-element output must yield >= V digits");
    digits
}

/// Generate a keypair from a 32-byte seed. The seed must be fresh,
/// high-entropy, and used for exactly one keypair -- as with any one-time
/// signature scheme, reusing a seed (or signing twice with the resulting
/// secret key) breaks security.
pub fn keygen(seed: &[u8; 32]) -> (SecretKey, PublicKey) {
    let perm16 = crate::poseidon2::perm16();
    let perm24 = crate::poseidon2::perm24();
    let seed_elems = seed_to_elements(seed);

    let mut param_input = [BabyBear::ZERO; 16];
    param_input[0..SEED_LEN].copy_from_slice(&seed_elems);
    param_input[8] = BabyBear::new(TAG_PARAM);
    let param: Param = perm16.compress(param_input);

    let mut chains = [[BabyBear::ZERO; CHAIN_LEN]; V];
    for (i, chain) in chains.iter_mut().enumerate() {
        let mut secret_input = [BabyBear::ZERO; 16];
        secret_input[0..SEED_LEN].copy_from_slice(&seed_elems);
        secret_input[8] = BabyBear::new(TAG_SECRET);
        secret_input[9] = BabyBear::new(i as u32);
        *chain = perm16.compress(secret_input);
    }

    let mut tops = [[BabyBear::ZERO; CHAIN_LEN]; V];
    for i in 0..V {
        let mut value = chains[i];
        for step in 0..CHAIN_STEPS {
            value = chain_step(perm24, &param, i, step, value);
        }
        tops[i] = value;
    }

    (SecretKey { param, chains }, PublicKey { param, tops })
}

/// Sign a (pre-hashed, 8-element) message digest. Internally retries with an
/// incrementing public randomizer until the derived digit vector sums to
/// exactly `TARGET_SUM`; for the Hashing-Optimized parameters this succeeds
/// within a handful of attempts in the overwhelming majority of cases, and
/// `None` is returned only in the astronomically unlikely event that
/// `MAX_TRIALS` attempts all fail.
pub fn sign(sk: &SecretKey, message_digest: [BabyBear; 8]) -> Option<Signature> {
    let perm24 = crate::poseidon2::perm24();

    for trial in 0..MAX_TRIALS {
        let mut randomizer = [BabyBear::ZERO; RAND_LEN];
        randomizer[0] = BabyBear::new(trial);

        let digits = derive_digits(&sk.param, message_digest, randomizer);
        if digits.iter().sum::<u32>() != TARGET_SUM {
            continue;
        }

        let mut values = [[BabyBear::ZERO; CHAIN_LEN]; V];
        for i in 0..V {
            let mut value = sk.chains[i];
            for step in 0..digits[i] {
                value = chain_step(perm24, &sk.param, i, step, value);
            }
            values[i] = value;
        }
        return Some(Signature { randomizer, values });
    }
    None
}

/// Verify a signature against a public key and (pre-hashed, 8-element)
/// message digest.
pub fn verify(pk: &PublicKey, message_digest: [BabyBear; 8], sig: &Signature) -> bool {
    let perm24 = crate::poseidon2::perm24();

    let digits = derive_digits(&pk.param, message_digest, sig.randomizer);
    if digits.iter().sum::<u32>() != TARGET_SUM {
        return false;
    }

    for i in 0..V {
        let mut value = sig.values[i];
        for step in digits[i]..CHAIN_STEPS {
            value = chain_step(perm24, &pk.param, i, step, value);
        }
        if value != pk.tops[i] {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    #[test]
    fn roundtrip_verifies() {
        let (sk, pk) = keygen(&seed(1));
        let digest = hash_message(b"hello wots");
        let sig = sign(&sk, digest).expect("signing should succeed within MAX_TRIALS");
        assert!(verify(&pk, digest, &sig));
    }

    #[test]
    fn public_key_len_matches_actual_encoded_length() {
        let (_, pk) = keygen(&seed(1));
        assert_eq!(pk.to_bytes().len(), PUBLIC_KEY_LEN);
    }

    #[test]
    fn wrong_message_rejected() {
        let (sk, pk) = keygen(&seed(2));
        let digest = hash_message(b"message A");
        let other_digest = hash_message(b"message B");
        let sig = sign(&sk, digest).unwrap();
        assert!(!verify(&pk, other_digest, &sig));
    }

    #[test]
    fn tampered_chain_value_rejected() {
        let (sk, pk) = keygen(&seed(3));
        let digest = hash_message(b"tamper test");
        let mut sig = sign(&sk, digest).unwrap();
        sig.values[0][0] = sig.values[0][0] + BabyBear::new(1);
        assert!(!verify(&pk, digest, &sig));
    }

    #[test]
    fn tampered_randomizer_rejected() {
        let (sk, pk) = keygen(&seed(4));
        let digest = hash_message(b"tamper randomizer");
        let mut sig = sign(&sk, digest).unwrap();
        sig.randomizer[0] = sig.randomizer[0] + BabyBear::new(1);
        assert!(!verify(&pk, digest, &sig));
    }

    #[test]
    fn different_seeds_give_different_keys() {
        let (_, pk_a) = keygen(&seed(5));
        let (_, pk_b) = keygen(&seed(6));
        assert_ne!(pk_a.param, pk_b.param);
        assert_ne!(pk_a.tops[0], pk_b.tops[0]);
    }

    #[test]
    fn digits_always_sum_to_target() {
        let (sk, _) = keygen(&seed(7));
        for msg in [&b"a"[..], &b"bb"[..], &b"ccc"[..]] {
            let digest = hash_message(msg);
            let sig = sign(&sk, digest).unwrap();
            let digits = derive_digits(&sk.param, digest, sig.randomizer);
            assert_eq!(digits.iter().sum::<u32>(), TARGET_SUM);
            assert!(digits.iter().all(|&d| d < W));
        }
    }

    /// Simulates an actual signer/verifier split: the signer's `SecretKey`
    /// and the original `PublicKey`/`Signature` structs are dropped before
    /// "verification," leaving only the raw bytes a verifier running in a
    /// separate process would actually have received. This is the concrete
    /// check that the verifier never needs -- and structurally cannot use --
    /// anything beyond the public key and signature bytes.
    #[test]
    fn verifier_works_from_serialized_bytes_alone() {
        let pk_bytes;
        let sig_bytes;
        let digest = hash_message(b"sent over the wire");
        {
            let (sk, pk) = keygen(&seed(8));
            let sig = sign(&sk, digest).unwrap();
            pk_bytes = pk.to_bytes();
            sig_bytes = sig.to_bytes();
            // sk, pk, and sig all go out of scope here.
        }

        let pk = PublicKey::from_bytes(&pk_bytes).expect("valid public key bytes");
        let sig = Signature::from_bytes(&sig_bytes).expect("valid signature bytes");
        assert!(verify(&pk, digest, &sig));

        // Corrupting one byte of the serialized public key must break
        // verification -- confirms the bytes are actually load-bearing, not
        // just round-tripped.
        let mut tampered = pk_bytes.clone();
        tampered[0] ^= 1;
        let bad_pk = PublicKey::from_bytes(&tampered).unwrap();
        assert!(!verify(&bad_pk, digest, &sig));
    }
}

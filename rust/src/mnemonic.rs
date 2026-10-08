//! The wallet's backup words: the 32-byte keychain seed as 24 BIP39
//! English words (`docs/RECOVERY.md`, step 1).
//!
//! The seed *is* the BIP39 entropy -- 256 bits, plus an 8-bit checksum
//! (the first byte of its SHA-256), split into 24 11-bit word indices.
//! There's no PBKDF2 stretching into a 64-byte BIP39 "seed": the keychain
//! takes 32 bytes, so words and seed map one-to-one, and the same words
//! give the same wallet in any software that follows this rule. (They
//! would *not* give the same keys in a Bitcoin wallet, which stretches
//! them -- and its keys aren't WOTS keys anyway.)
//!
//! Parsing is forgiving about what doesn't matter -- case and spacing,
//! and a word may be shortened to its first four letters (unique in the
//! BIP39 list; how words are often stamped on metal backups) -- and
//! strict about what does: exactly 24 known words with a valid checksum.
//!
//! SHA-256 is only needed for the checksum, so it's implemented here
//! rather than taken as a dependency.

#![allow(dead_code)]

const WORDLIST: &str = include_str!("bip39_english.txt");

pub const WORDS: usize = 24;

/// The 2048 words, in order.
fn wordlist() -> &'static [&'static str; 2048] {
    static LIST: std::sync::OnceLock<[&str; 2048]> = std::sync::OnceLock::new();
    LIST.get_or_init(|| {
        let words: Vec<&str> = WORDLIST.lines().collect();
        words.try_into().expect("the BIP39 list has 2048 words")
    })
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Not 24 words.
    WordCount(usize),
    /// The word at this position (from 1) isn't in the list, and isn't a
    /// four-letter (or longer) prefix of exactly one word.
    UnknownWord(usize, String),
    /// Every word is valid, but they don't fit together: one is wrong or
    /// out of order.
    Checksum,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::WordCount(n) => write!(f, "expected {WORDS} words, got {n}"),
            Error::UnknownWord(i, w) => write!(f, "word {i} ({w:?}) isn't a backup word"),
            Error::Checksum => write!(f, "the words don't fit together -- one is wrong or out of order"),
        }
    }
}

impl std::error::Error for Error {}

/// The 24 words for `seed`.
pub fn to_words(seed: &[u8; 32]) -> Vec<&'static str> {
    let checksum = sha256(seed)[0];
    let bits = |i: usize| -> u16 {
        let byte = if i < 256 { seed[i / 8] } else { checksum };
        ((byte >> (7 - i % 8)) & 1) as u16
    };
    (0..WORDS).map(|w| wordlist()[(0..11).fold(0u16, |acc, b| acc << 1 | bits(w * 11 + b)) as usize]).collect()
}

/// The 24 words for `seed`, space-separated.
pub fn to_phrase(seed: &[u8; 32]) -> String {
    to_words(seed).join(" ")
}

/// A phrase for people: four rows of six words, nothing else -- easy to
/// write down in order, and to copy and paste (parsing takes any spacing
/// and line breaks).
pub fn display(phrase: &str) -> String {
    let words: Vec<&str> = phrase.split_whitespace().collect();
    words.chunks(6).map(|row| row.join(" ")).collect::<Vec<_>>().join("\n")
}

/// The seed for a phrase of 24 words.
pub fn from_phrase(phrase: &str) -> Result<[u8; 32], Error> {
    let words: Vec<String> = phrase.split_whitespace().map(str::to_lowercase).collect();
    if words.len() != WORDS {
        return Err(Error::WordCount(words.len()));
    }
    let mut bits = Vec::with_capacity(WORDS * 11);
    for (i, word) in words.iter().enumerate() {
        let index = lookup(word).ok_or_else(|| Error::UnknownWord(i + 1, word.clone()))?;
        bits.extend((0..11).rev().map(|b| (index >> b) & 1 == 1));
    }
    let byte = |chunk: &[bool]| chunk.iter().fold(0u8, |acc, &b| acc << 1 | b as u8);
    let mut seed = [0u8; 32];
    for (s, chunk) in seed.iter_mut().zip(bits[..256].chunks(8)) {
        *s = byte(chunk);
    }
    if byte(&bits[256..]) != sha256(&seed)[0] {
        return Err(Error::Checksum);
    }
    Ok(seed)
}

/// A word's index: an exact match, or a prefix of at least four letters
/// matching exactly one word.
fn lookup(word: &str) -> Option<u16> {
    let list = wordlist();
    if let Ok(i) = list.binary_search(&word) {
        return Some(i as u16);
    }
    if word.len() < 4 {
        return None;
    }
    let first = list.partition_point(|w| *w < word);
    match list[first..].iter().take_while(|w| w.starts_with(word)).count() {
        1 => Some(first as u16),
        _ => None,
    }
}

/// SHA-256 (FIPS 180-4).
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finish()
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be,
    0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa,
    0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85,
    0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
    0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Streaming SHA-256. `Clone`, so HMAC can start from precomputed keyed
/// states.
#[derive(Clone)]
struct Sha256 {
    h: [u32; 8],
    block: [u8; 64],
    filled: usize,
    length: u64,
}

impl Sha256 {
    fn new() -> Self {
        Sha256 {
            h: [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19],
            block: [0; 64],
            filled: 0,
            length: 0,
        }
    }

    fn update(&mut self, mut data: &[u8]) {
        self.length += data.len() as u64;
        while !data.is_empty() {
            let take = (64 - self.filled).min(data.len());
            self.block[self.filled..self.filled + take].copy_from_slice(&data[..take]);
            self.filled += take;
            data = &data[take..];
            if self.filled == 64 {
                let block = self.block;
                self.compress(&block);
                self.filled = 0;
            }
        }
    }

    fn finish(mut self) -> [u8; 32] {
        let bits = self.length * 8;
        self.update(&[0x80]);
        while self.filled != 56 {
            self.update(&[0]);
        }
        self.update(&bits.to_be_bytes());
        let mut out = [0u8; 32];
        for (o, x) in out.chunks_mut(4).zip(self.h) {
            o.copy_from_slice(&x.to_be_bytes());
        }
        out
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes(word.try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = self.h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (x, y) in self.h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *x = x.wrapping_add(y);
        }
    }
}

/// HMAC-SHA256 (RFC 2104), keyed once: the inner and outer states after
/// absorbing the padded key, reused for every message.
#[derive(Clone)]
struct HmacSha256 {
    inner: Sha256,
    outer: Sha256,
}

impl HmacSha256 {
    fn new(key: &[u8]) -> Self {
        let mut block = [0u8; 64];
        if key.len() > 64 {
            block[..32].copy_from_slice(&sha256(key));
        } else {
            block[..key.len()].copy_from_slice(key);
        }
        let (mut inner, mut outer) = (Sha256::new(), Sha256::new());
        inner.update(&block.map(|b| b ^ 0x36));
        outer.update(&block.map(|b| b ^ 0x5c));
        HmacSha256 { inner, outer }
    }

    fn mac(&self, message: &[u8]) -> [u8; 32] {
        let mut inner = self.inner.clone();
        inner.update(message);
        let mut outer = self.outer.clone();
        outer.update(&inner.finish());
        outer.finish()
    }
}

/// PBKDF2-HMAC-SHA256 (RFC 8018), one 32-byte block.
fn pbkdf2_sha256(password: &[u8], salt: &[u8], rounds: u32) -> [u8; 32] {
    let prf = HmacSha256::new(password);
    let mut u = prf.mac(&[salt, &1u32.to_be_bytes()].concat());
    let mut out = u;
    for _ in 1..rounds {
        u = prf.mac(&u);
        for (o, x) in out.iter_mut().zip(u) {
            *o ^= x;
        }
    }
    out
}

/// How hard a passphrase is stretched (PBKDF2 rounds): what makes guessing
/// passphrases for a set of stolen words slow. Fixed forever -- changing
/// it changes every passphrase wallet's keys.
pub const PASSPHRASE_ROUNDS: u32 = 100_000;

const PASSPHRASE_SALT: &[u8] = b"tabernacle-passphrase-v1";

/// The keychain seed for backup words (as `entropy`) and an optional
/// passphrase. Without one (`""`), the seed *is* the entropy -- words and
/// seed map one-to-one, as before passphrases existed. With one:
///
/// ```text
/// seed = PBKDF2-HMAC-SHA256(passphrase, "tabernacle-passphrase-v1" ‖ entropy, PASSPHRASE_ROUNDS)
/// ```
///
/// Any passphrase gives *a* valid wallet -- a wrong one just gives an
/// empty one (as in BIP39), so there's nothing to tell an attacker which
/// guess was right short of finding funds.
pub fn seed_from(entropy: &[u8; 32], passphrase: &str) -> [u8; 32] {
    if passphrase.is_empty() {
        return *entropy;
    }
    pbkdf2_sha256(passphrase.as_bytes(), &[PASSPHRASE_SALT, entropy].concat(), PASSPHRASE_ROUNDS)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn sha256_matches_known_digests() {
        assert_eq!(hex(&sha256(b"")), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(hex(&sha256(b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(
            hex(&sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        // The published hash of the official BIP39 English list: ours is
        // the real list, unaltered.
        assert_eq!(hex(&sha256(WORDLIST.as_bytes())), "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda");
    }

    #[test]
    fn hmac_and_pbkdf2_match_published_vectors() {
        // RFC 4231, test case 2.
        assert_eq!(hex(&HmacSha256::new(b"Jefe").mac(b"what do ya want for nothing?")), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
        // PBKDF2-HMAC-SHA256 ("password", "salt").
        assert_eq!(hex(&pbkdf2_sha256(b"password", b"salt", 1)), "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b");
        assert_eq!(hex(&pbkdf2_sha256(b"password", b"salt", 2)), "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43");
        assert_eq!(hex(&pbkdf2_sha256(b"password", b"salt", 4096)), "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a");
        // Streaming in pieces matches one shot, across block boundaries.
        let data: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let mut h = Sha256::new();
        for piece in data.chunks(37) {
            h.update(piece);
        }
        assert_eq!(h.finish(), sha256(&data));
    }

    #[test]
    fn passphrases_change_the_seed_and_none_keeps_it() {
        let entropy = sha256(b"passphrase entropy");
        assert_eq!(seed_from(&entropy, ""), entropy, "no passphrase: the words are the seed");
        let a = seed_from(&entropy, "correct horse");
        assert_ne!(a, entropy);
        assert_eq!(a, seed_from(&entropy, "correct horse"));
        assert_ne!(a, seed_from(&entropy, "correct horsE"));
        assert_ne!(a, seed_from(&sha256(b"other words"), "correct horse"));
    }

    #[test]
    fn bip39_test_vectors() {
        // From the BIP39 reference vectors (256-bit entropy).
        let vectors: [([u8; 32], &str); 4] = [
            ([0x00; 32], "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art"),
            ([0x7f; 32], "legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth useful legal winner thank year wave sausage worth title"),
            ([0x80; 32], "letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic avoid letter advice cage absurd amount doctor acoustic bless"),
            ([0xff; 32], "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo vote"),
        ];
        for (seed, phrase) in vectors {
            assert_eq!(to_phrase(&seed), phrase);
            assert_eq!(from_phrase(phrase), Ok(seed));
        }
    }

    #[test]
    fn the_display_form_is_plain_words_that_parse_back() {
        let seed = sha256(b"display");
        let shown = display(&to_phrase(&seed));
        assert_eq!(shown.lines().count(), 4);
        assert!(shown.lines().all(|l| l.split(' ').count() == 6));
        assert!(!shown.chars().any(|c| c.is_ascii_digit()));
        assert_eq!(from_phrase(&shown), Ok(seed), "pasted as shown, it restores");
    }

    #[test]
    fn random_seeds_round_trip() {
        for i in 0..200u32 {
            let seed = sha256(&i.to_le_bytes());
            assert_eq!(from_phrase(&to_phrase(&seed)), Ok(seed));
        }
    }

    #[test]
    fn parsing_forgives_case_spacing_and_four_letter_prefixes() {
        let seed = sha256(b"prefixes");
        let words = to_words(&seed);
        let messy = words.iter().map(|w| w.to_uppercase()).collect::<Vec<_>>().join("  \n\t");
        assert_eq!(from_phrase(&messy), Ok(seed));
        let short = words.iter().map(|w| &w[..w.len().min(4)]).collect::<Vec<_>>().join(" ");
        assert_eq!(from_phrase(&short), Ok(seed));
    }

    #[test]
    fn mistakes_are_caught() {
        let seed = sha256(b"mistakes");
        let words = to_words(&seed);
        assert_eq!(from_phrase(&words[..23].join(" ")), Err(Error::WordCount(23)));
        let mut bad = words.clone();
        bad[4] = "bitcoinz";
        assert_eq!(from_phrase(&bad.join(" ")), Err(Error::UnknownWord(5, "bitcoinz".into())));
        // Too short to be a prefix, or a prefix of several words.
        bad[4] = "ab";
        assert!(matches!(from_phrase(&bad.join(" ")), Err(Error::UnknownWord(5, _))));
        // Swapping two different words breaks the checksum almost always
        // (1 in 256 by chance); this seed's first two words differ and do.
        let mut swapped = words.clone();
        assert_ne!(swapped[0], swapped[1]);
        swapped.swap(0, 1);
        assert_eq!(from_phrase(&swapped.join(" ")), Err(Error::Checksum));
        // A single wrong (but valid) word.
        let mut wrong = words.clone();
        wrong[23] = if wrong[23] == "zoo" { "zone" } else { "zoo" };
        assert_eq!(from_phrase(&wrong.join(" ")), Err(Error::Checksum));
    }
}

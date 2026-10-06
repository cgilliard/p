//! The wallet: a keychain's seed, the outputs it owns, and the slates it's
//! part of -- persisted in its own LMDB environment, separate from
//! consensus state (wiping chain data never touches keys or slates).
//!
//! # Knowing what we own
//!
//! On chain an output is just a commitment, so the wallet records every
//! output it expects to own as it creates it: a mining reward, the change
//! of a payment it sends, the output it adds when receiving (`slate`).
//! Each record carries the key it pays to (`keychain::KeyId`), the amount,
//! and the wallet's own intent for it -- free, locked into an unfinished
//! slate, or signed away.
//!
//! What the *chain* says about each output isn't stored as history; it's
//! re-derived on every `refresh` from two facts: is the commitment
//! currently unspent on chain, and have we signed a spend of it. Only we
//! hold our keys, so an output of ours can only leave the unspent set
//! through a transaction we signed:
//!
//! | signed a spend? | unspent on chain? | status |
//! |---|---|---|
//! | no | yes | confirmed (spendable once mature) |
//! | no | no | pending (not on chain yet, or reorged out) |
//! | yes | yes | spending (our transaction isn't confirmed yet) |
//! | yes | no | spent |
//!
//! That makes the wallet self-healing across reorgs, with no block replay
//! to get wrong. (One case it can't tell apart: an output we signed away,
//! then lost to a reorg before our transaction confirmed, reads as spent.)
//!
//! # One-time keys
//!
//! Keys are WOTS one-time keys, so the wallet is careful about two things:
//!
//! - **Each key index is handed out once**, and the next index is
//!   committed in the same transaction as whatever uses the key.
//! - **Each slate is signed at most once.** `finalize` stores the signed
//!   transaction before returning it, and returns that same stored
//!   transaction if asked again -- never a second signature.

#![allow(dead_code)]

use std::path::Path;

use heed::Database;
use heed::types::Bytes;

use crate::keychain::{KeyId, Keychain};
use crate::output::Output;
use crate::recovery::{self, NONCE_LEN, ViewKey};
use crate::slate::{self, Slate};
use crate::storage::Storage;
use crate::transaction::Transaction;

/// All keys come from one account for now.
const ACCOUNT: u32 = 0;

/// The most inputs a payment may spend: what one chunk of a tree-proven
/// block holds (`prover::CHUNK_SHAPE`).
pub const MAX_INPUTS: usize = crate::prover::CHUNK_SHAPE.inputs;

/// Confirmations before a mining reward may be spent, so a reorg can't
/// erase coins that were already spent onward. Wallet policy, not
/// consensus.
pub const COINBASE_MATURITY: u64 = 10;

const SEED_KEY: &[u8] = b"seed";
const NEXT_INDEX_KEY: &[u8] = b"next_index";
/// Present while a wallet restored from its backup words hasn't yet
/// scanned a fully synced chain (`restore`, `finish_recovery`).
const RECOVERING_KEY: &[u8] = b"recovering";
/// The backup words' entropy (the seed is derived from it and, if set, a
/// passphrase -- `mnemonic::seed_from`), and whether a passphrase was.
/// Absent in wallets made before passphrases: their seed is the entropy.
const ENTROPY_KEY: &[u8] = b"backup_entropy";
const PASSPHRASE_KEY: &[u8] = b"backup_passphrase";

/// After recovery, keys are handed out from this far past the highest
/// index found on chain -- covering keys the lost wallet handed out that
/// never confirmed (unanswered slates, rewards for blocks others won).
pub const RECOVERY_INDEX_MARGIN: u32 = 1000;

/// The margin instead, on a chain without spent outputs' history (a
/// fast-synced node: its state holds only unspent outputs). Recovery then
/// can't see keys whose outputs were all spent -- which signed, and must
/// never be handed out again -- so it leaves a far wider gap. Indices are
/// 32-bit, so the gap costs nothing.
pub const RECOVERY_INDEX_MARGIN_WITHOUT_HISTORY: u32 = 100_000;

/// A recovered output can't be spent until this many blocks after
/// recovery: if the lost wallet had signed a spend of it that's still in
/// flight, that spend gets time to show up (`observe_spend`) or confirm --
/// signing a *different* spend of it would reveal a second one-time
/// signature, and with it the key.
pub const RECOVERY_HOLD_BLOCKS: u64 = 10;

/// What the chain can tell the wallet.
pub trait ChainView {
    /// The active chain's height.
    fn tip_height(&self) -> u64;
    /// Whether `commitment` is an unspent output of the active chain.
    fn is_unspent(&self, commitment: &[u8; 32]) -> bool;
    /// The height of the block that created `commitment` on the active
    /// chain, and its recovery nonce -- if known (`None` falls back to
    /// "seen now", and skips the nonce check).
    fn output_record(&self, _commitment: &[u8; 32]) -> Option<(u64, [u8; NONCE_LEN])> {
        None
    }
    /// Whether this view knows every output the chain ever created, spent
    /// ones included -- false on a node that fast-synced from a snapshot of
    /// unspent outputs (recovery then uses a wider key margin).
    fn has_full_history(&self) -> bool {
        true
    }
    /// Call `f(commitment, height, nonce, unspent)` for every output the
    /// active chain has created -- what recovery scans. Returns whether
    /// the whole scan succeeded. (A view that can't offer this fails.)
    fn for_each_output(&self, _f: &mut dyn FnMut([u8; 32], u64, [u8; NONCE_LEN], bool)) -> bool {
        false
    }
}

/// What `finish_recovery` found.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Recovered {
    /// Our outputs found on chain, spent or not.
    pub outputs: usize,
    /// How many of them are unspent, and their total.
    pub unspent: usize,
    pub amount: u64,
    /// Where key handout resumes.
    pub next_index: u32,
    /// Recovered outputs are spendable from this height.
    pub spendable_from: u64,
}

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    Corrupt(&'static str),
    Slate(slate::Error),
    /// Not enough spendable coins (within `MAX_INPUTS` inputs).
    InsufficientFunds { spendable: u64, needed: u64 },
    UnknownSlate,
    /// The slate is ours, but not in a state this step applies to.
    WrongSlateState(&'static str),
    /// The slate was already finalized with a different response.
    AlreadyFinalized,
    /// `restore` into a directory that already holds a wallet.
    Exists,
    /// Restored from backup words, and still waiting for a synced chain
    /// to scan (`finish_recovery`): no keys are handed out until then.
    Recovering,
}

impl From<crate::storage::Error> for Error {
    fn from(e: crate::storage::Error) -> Self {
        Error::Storage(e)
    }
}

impl From<heed::Error> for Error {
    fn from(e: heed::Error) -> Self {
        Error::Heed(e)
    }
}

impl From<slate::Error> for Error {
    fn from(e: slate::Error) -> Self {
        Error::Slate(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use crate::output::format_amount;
        match self {
            Error::Storage(e) => write!(f, "wallet storage: {e}"),
            Error::Heed(e) => write!(f, "wallet storage: {e}"),
            Error::Corrupt(what) => write!(f, "corrupt wallet data: {what}"),
            Error::Slate(e) => write!(f, "{e}"),
            Error::InsufficientFunds { spendable, needed } => write!(
                f,
                "not enough spendable funds: {} available (in at most {MAX_INPUTS} outputs), {} needed",
                format_amount(*spendable),
                format_amount(*needed)
            ),
            Error::UnknownSlate => write!(f, "this wallet has no record of that slate"),
            Error::WrongSlateState(what) => write!(f, "{what}"),
            Error::AlreadyFinalized => write!(f, "that slate was already finalized with a different response"),
            Error::Exists => write!(f, "a wallet already exists there -- restore into a new directory"),
            Error::Recovering => write!(f, "the wallet is still being recovered (waiting for the chain to sync)"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// How an owned output came about.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Origin {
    Mined = 0,
    Change = 1,
    Received = 2,
    /// Found on chain by recovery: we can't tell whether it was a mining
    /// reward, so it's given a reward's maturity.
    Recovered = 3,
}

/// The wallet's own intent for an output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lock {
    Free,
    /// An input of this unfinished slate (cancelling frees it).
    Locked([u8; 16]),
    /// An input of this slate's signed transaction (permanent).
    Signed([u8; 16]),
    /// Recovered: not spendable until the chain reaches this height
    /// (`RECOVERY_HOLD_BLOCKS`); otherwise like `Free`.
    Held(u64),
}

/// An output the wallet owns (or expects to).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OwnedOutput {
    pub commitment: [u8; 32],
    pub key: KeyId,
    pub amount: u64,
    pub origin: Origin,
    pub lock: Lock,
    /// The height of the block that created it, while it's on chain
    /// (from the chain's output index; a chain view without one gives
    /// the height `refresh` first saw it at). Confirmations count from
    /// here.
    pub seen_height: Option<u64>,
    /// Spent on chain -- by a transaction we signed, or (for an output
    /// the chain knows it created) by anyone (`refresh`).
    pub spent: bool,
}

/// What the wallet makes of an output, given the chain's tip.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Status {
    /// Not on chain (yet).
    Pending,
    /// On chain with this many confirmations; spendable if mature.
    Confirmed { confirmations: u64, mature: bool },
    /// An input of an unfinished slate.
    Locked,
    /// Signed away, not yet confirmed.
    Spending,
    Spent,
    /// Recovered and on chain, but not spendable before height `until`
    /// (`RECOVERY_HOLD_BLOCKS`).
    Held { confirmations: u64, until: u64 },
}

impl OwnedOutput {
    pub fn status(&self, tip_height: u64) -> Status {
        match (self.lock, self.seen_height, self.spent) {
            (_, _, true) => Status::Spent,
            (Lock::Signed(_), _, false) => Status::Spending,
            (Lock::Locked(_), _, _) => Status::Locked,
            (Lock::Free | Lock::Held(_), None, _) => Status::Pending,
            (Lock::Free | Lock::Held(_), Some(h), _) => {
                let confirmations = tip_height.saturating_sub(h) + 1;
                // The hold (from recovery, at a height no earlier than the
                // output's) always outlasts maturity, so it's what to show.
                if let Lock::Held(until) = self.lock
                    && tip_height < until
                {
                    return Status::Held { confirmations, until };
                }
                let reward_like = matches!(self.origin, Origin::Mined | Origin::Recovered);
                let mature = !reward_like || confirmations >= COINBASE_MATURITY;
                Status::Confirmed { confirmations, mature }
            }
        }
    }

    fn to_bytes(self) -> Vec<u8> {
        let mut out = self.key.to_bytes().to_vec();
        out.extend(self.amount.to_le_bytes());
        out.push(self.origin as u8);
        match self.lock {
            Lock::Free => out.extend([0u8; 17]),
            Lock::Locked(id) => {
                out.push(1);
                out.extend(id);
            }
            Lock::Signed(id) => {
                out.push(2);
                out.extend(id);
            }
            Lock::Held(until) => {
                out.push(3);
                out.extend(until.to_le_bytes());
                out.extend([0u8; 8]);
            }
        }
        out.extend(self.seen_height.map_or(u64::MAX, |h| h).to_le_bytes());
        out.push(self.spent as u8);
        out
    }

    fn from_bytes(commitment: [u8; 32], bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 8 + 8 + 1 + 17 + 8 + 1 {
            return None;
        }
        let origin = match bytes[16] {
            0 => Origin::Mined,
            1 => Origin::Change,
            2 => Origin::Received,
            3 => Origin::Recovered,
            _ => return None,
        };
        let id: [u8; 16] = bytes[18..34].try_into().unwrap();
        let lock = match bytes[17] {
            0 => Lock::Free,
            1 => Lock::Locked(id),
            2 => Lock::Signed(id),
            3 => Lock::Held(u64::from_le_bytes(id[..8].try_into().unwrap())),
            _ => return None,
        };
        let seen = u64::from_le_bytes(bytes[34..42].try_into().unwrap());
        Some(OwnedOutput {
            commitment,
            key: KeyId::from_bytes(&bytes[..8])?,
            amount: u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            origin,
            lock,
            seen_height: (seen != u64::MAX).then_some(seen),
            spent: bytes[42] == 1,
        })
    }
}

/// Our side of a slate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Role {
    Sender = 0,
    Receiver = 1,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SlateState {
    /// Sender: S1 written, waiting for the response.
    Sent = 0,
    /// Receiver: S2 written.
    Received = 1,
    /// Sender: signed; the transaction is stored.
    Finalized = 2,
    /// Sender: abandoned before signing; inputs freed.
    Cancelled = 3,
}

/// A slate the wallet is part of.
#[derive(Clone, Debug)]
pub struct SlateRecord {
    pub role: Role,
    pub state: SlateState,
    /// The sender's S1, or the receiver's S2.
    pub slate: Slate,
    /// The signed transaction (sender, once finalized).
    pub transaction: Option<Transaction>,
}

impl SlateRecord {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![self.role as u8, self.state as u8];
        let slate = self.slate.to_bytes();
        out.extend((slate.len() as u32).to_le_bytes());
        out.extend(slate);
        if let Some(tx) = &self.transaction {
            out.extend(tx.to_bytes());
        }
        out
    }

    fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let role = match *bytes.first()? {
            0 => Role::Sender,
            1 => Role::Receiver,
            _ => return None,
        };
        let state = match *bytes.get(1)? {
            0 => SlateState::Sent,
            1 => SlateState::Received,
            2 => SlateState::Finalized,
            3 => SlateState::Cancelled,
            _ => return None,
        };
        let len = u32::from_le_bytes(bytes.get(2..6)?.try_into().unwrap()) as usize;
        let slate = Slate::from_bytes(bytes.get(6..6 + len)?).ok()?;
        let rest = bytes.get(6 + len..)?;
        let transaction = if rest.is_empty() { None } else { Some(Transaction::from_bytes(rest)?) };
        Some(SlateRecord {
            role,
            state,
            slate,
            transaction,
        })
    }
}

/// Totals, by status.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Balance {
    /// Confirmed, mature and free: what `send` can use.
    pub spendable: u64,
    /// Confirmed mining rewards not yet mature.
    pub immature: u64,
    /// Expected but not on chain yet: incoming payments and change.
    /// (Rewards of blocks still being mined don't count.)
    pub pending: u64,
    /// In unfinished slates, or signed away and awaiting confirmation.
    pub locked: u64,
    /// Recovered, held until `held_until` (`RECOVERY_HOLD_BLOCKS`).
    pub held: u64,
    pub held_until: u64,
}

impl Balance {
    pub fn total(&self) -> u64 {
        self.spendable + self.immature + self.pending + self.locked + self.held
    }
}

pub struct Wallet {
    storage: Storage,
    keychain: Keychain,
    meta: Database<Bytes, Bytes>,
    outputs: Database<Bytes, Bytes>,
    slates: Database<Bytes, Bytes>,
    /// Signed transactions that aren't slates (`self_transfer`), by id.
    transactions: Database<Bytes, Bytes>,
    /// Seals every output we create with a recovery nonce (`recovery`).
    view_key: ViewKey,
}

impl Wallet {
    /// Open the wallet in `dir`, creating it -- with a new random seed --
    /// if it doesn't exist. The directory is made private to the user.
    pub fn open(dir: &Path) -> Result<Wallet> {
        Self::open_inner(dir, None, None)
    }

    /// Create a new wallet in `dir` (which must not hold one) with fresh
    /// backup words and a passphrase: restoring it takes both.
    pub fn create_with_passphrase(dir: &Path, passphrase: &str) -> Result<Wallet> {
        if dir.join("data.mdb").exists() {
            return Err(Error::Exists);
        }
        let entropy = crate::keychain::random_bytes();
        let keychain = Keychain::from_seed(crate::mnemonic::seed_from(&entropy, passphrase));
        Self::open_inner(dir, Some(keychain), Some((entropy, !passphrase.is_empty())))
    }

    /// Open the wallet in `dir`, creating it from `keychain`'s seed if it
    /// doesn't exist (restore, or tests). An existing wallet must have the
    /// same seed.
    pub fn open_with(dir: &Path, keychain: Keychain) -> Result<Wallet> {
        Self::open_inner(dir, Some(keychain), None)
    }

    /// `backup`, for a wallet created here: its words' entropy, and whether
    /// a passphrase was used (`None`: the seed is the entropy).
    fn open_inner(dir: &Path, keychain: Option<Keychain>, backup: Option<([u8; 32], bool)>) -> Result<Wallet> {
        std::fs::create_dir_all(dir).map_err(crate::storage::Error::Io)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o700)).map_err(crate::storage::Error::Io)?;
        }
        let storage = Storage::open(dir)?;
        let meta = storage.database("wallet_meta")?;
        let outputs = storage.database("wallet_outputs")?;
        let slates = storage.database("wallet_slates")?;
        let transactions = storage.database("wallet_transactions")?;
        let mut wtxn = storage.write_txn()?;
        let keychain = match meta.get(&wtxn, SEED_KEY)? {
            Some(seed) => {
                let seed: [u8; 32] = seed.try_into().map_err(|_| Error::Corrupt("seed"))?;
                if keychain.as_ref().is_some_and(|k| k.seed() != &seed) {
                    return Err(Error::Corrupt("the wallet exists with a different seed"));
                }
                Keychain::from_seed(seed)
            }
            None => {
                let keychain = keychain.unwrap_or_else(Keychain::random);
                meta.put(&mut wtxn, SEED_KEY, keychain.seed())?;
                let (entropy, passphrase) = backup.unwrap_or((*keychain.seed(), false));
                meta.put(&mut wtxn, ENTROPY_KEY, &entropy)?;
                meta.put(&mut wtxn, PASSPHRASE_KEY, &[passphrase as u8])?;
                keychain
            }
        };
        wtxn.commit()?;
        Ok(Wallet {
            view_key: keychain.view_key(),
            storage,
            keychain,
            meta,
            outputs,
            slates,
            transactions,
        })
    }

    pub fn keychain(&self) -> &Keychain {
        &self.keychain
    }

    /// The 24 backup words, and whether restoring also takes a passphrase.
    pub fn backup_words(&self) -> Result<(String, bool)> {
        let rtxn = self.storage.read_txn()?;
        let Some(entropy) = self.meta.get(&rtxn, ENTROPY_KEY)? else {
            return Ok((self.keychain.phrase(), false));
        };
        let entropy: [u8; 32] = entropy.try_into().map_err(|_| Error::Corrupt("backup entropy"))?;
        let passphrase = self.meta.get(&rtxn, PASSPHRASE_KEY)?.is_some_and(|b| b == [1]);
        Ok((crate::mnemonic::to_phrase(&entropy), passphrase))
    }

    // ---- recovery (`docs/RECOVERY.md`) -----------------------------------

    /// Restore a wallet from its seed (the backup words) into `dir`, which
    /// must not already hold one. It starts **recovering**: it knows
    /// nothing yet and hands out no keys -- no mining, sending or
    /// receiving -- until `finish_recovery` has scanned a fully synced
    /// chain, since any key it handed out before then might be one the
    /// lost wallet already used.
    pub fn restore(dir: &Path, keychain: Keychain) -> Result<Wallet> {
        Self::restore_inner(dir, keychain, None)
    }

    /// `restore` from the backup words and passphrase (`""` for none).
    pub fn restore_from_words(dir: &Path, phrase: &str, passphrase: &str) -> Result<Wallet> {
        let entropy = crate::mnemonic::from_phrase(phrase).map_err(|_| Error::WrongSlateState("those aren't valid backup words"))?;
        let keychain = Keychain::from_seed(crate::mnemonic::seed_from(&entropy, passphrase));
        Self::restore_inner(dir, keychain, Some((entropy, !passphrase.is_empty())))
    }

    fn restore_inner(dir: &Path, keychain: Keychain, backup: Option<([u8; 32], bool)>) -> Result<Wallet> {
        if dir.join("data.mdb").exists() {
            return Err(Error::Exists);
        }
        let wallet = Self::open_inner(dir, Some(keychain), backup)?;
        let mut wtxn = wallet.storage.write_txn()?;
        wallet.meta.put(&mut wtxn, RECOVERING_KEY, &[1])?;
        wtxn.commit()?;
        Ok(wallet)
    }

    pub fn is_recovering(&self) -> Result<bool> {
        let rtxn = self.storage.read_txn()?;
        Ok(self.meta.get(&rtxn, RECOVERING_KEY)?.is_some())
    }

    /// Finish a `restore`, once `chain` is synced with the network: find
    /// every output of ours it ever created (each one's recovery nonce
    /// names its key and amount; `recovery::identify` confirms), record
    /// them, and resume key handout past every index ever used (plus
    /// `RECOVERY_INDEX_MARGIN`). Unspent ones are held for
    /// `RECOVERY_HOLD_BLOCKS`.
    pub fn finish_recovery(&self, chain: &impl ChainView) -> Result<Recovered> {
        let tip = chain.tip_height();
        let mut found = Vec::new();
        let scanned = chain.for_each_output(&mut |commitment, height, nonce, unspent| {
            if let Some((key, amount)) = recovery::identify(&self.keychain, &self.view_key, ACCOUNT, &commitment, &nonce) {
                found.push((commitment, key, amount, height, unspent));
            }
        });
        if !scanned {
            return Err(Error::Corrupt("couldn't scan the chain's outputs"));
        }
        let spendable_from = tip + RECOVERY_HOLD_BLOCKS;
        let mut report = Recovered { spendable_from, ..Default::default() };
        let mut wtxn = self.storage.write_txn()?;
        let mut max_index = None;
        for (commitment, key, amount, height, unspent) in found {
            max_index = max_index.max(Some(key.index));
            report.outputs += 1;
            if unspent {
                report.unspent += 1;
                report.amount += amount;
            }
            // Don't overwrite what we already know (a repeated call).
            if self.get_output(&wtxn, &commitment)?.is_some() {
                continue;
            }
            self.put_output(
                &mut wtxn,
                &OwnedOutput {
                    commitment,
                    key,
                    amount,
                    origin: Origin::Recovered,
                    lock: if unspent { Lock::Held(spendable_from) } else { Lock::Free },
                    seen_height: Some(height),
                    spent: !unspent,
                },
            )?;
        }
        let margin = if chain.has_full_history() {
            RECOVERY_INDEX_MARGIN
        } else {
            RECOVERY_INDEX_MARGIN_WITHOUT_HISTORY
        };
        let resume = max_index.map_or(0, |m| m.saturating_add(1)).saturating_add(margin);
        let current = match self.meta.get(&wtxn, NEXT_INDEX_KEY)? {
            Some(b) => u32::from_le_bytes(b.try_into().map_err(|_| Error::Corrupt("next index"))?),
            None => 0,
        };
        report.next_index = resume.max(current);
        self.meta.put(&mut wtxn, NEXT_INDEX_KEY, &report.next_index.to_le_bytes())?;
        self.meta.delete(&mut wtxn, RECOVERING_KEY)?;
        wtxn.commit()?;
        Ok(report)
    }

    /// Note a transaction someone (a peer, a copy of this wallet, or this
    /// wallet before it was lost and restored) has signed, if it spends
    /// any output of ours we haven't signed: mark those as signed away,
    /// and keep the transaction (resubmitted at startup like our own) --
    /// so we never sign a different spend of them. Any of its outputs
    /// sealed to us (its change, say) are recorded as expected, so they're
    /// ours once it confirms. Returns whether it spent outputs of ours.
    pub fn observe_spend(&self, tx: &Transaction) -> Result<bool> {
        let id = tx.id();
        let lock: [u8; 16] = id[..16].try_into().unwrap();
        let mut wtxn = self.storage.write_txn()?;
        let mut ours = false;
        for input in &tx.inputs {
            let commitment = Output::new(&input.pubkey, input.amount).commitment();
            if let Some(mut o) = self.get_output(&wtxn, &commitment)?
                && !matches!(o.lock, Lock::Signed(_))
            {
                o.lock = Lock::Signed(lock);
                self.put_output(&mut wtxn, &o)?;
                ours = true;
            }
        }
        if ours {
            self.transactions.put(&mut wtxn, &id, &tx.to_bytes())?;
            for output in &tx.outputs {
                let commitment = output.commitment();
                let Some((key, amount)) = recovery::identify(&self.keychain, &self.view_key, ACCOUNT, &commitment, &output.nonce) else {
                    continue;
                };
                if self.get_output(&wtxn, &commitment)?.is_none() {
                    let expected = OwnedOutput {
                        commitment,
                        key,
                        amount,
                        origin: Origin::Recovered,
                        lock: Lock::Free,
                        seen_height: None,
                        spent: false,
                    };
                    self.put_output(&mut wtxn, &expected)?;
                }
            }
            wtxn.commit()?;
        }
        Ok(ours)
    }

    /// The output paying `amount` to our key `key`, sealed with its
    /// recovery nonce -- how every output this wallet creates is made, so
    /// the seed alone can find it again (`docs/RECOVERY.md`).
    fn sealed_output(&self, key: KeyId, amount: u64) -> Output {
        let output = self.keychain.output(key, amount);
        let nonce = recovery::seal(&self.view_key, &output.commitment(), key.index, amount);
        output.with_nonce(nonce)
    }

    /// Hand out the next unused key, recording that in `wtxn` -- committed
    /// together with whatever uses it, so a key is never handed out twice.
    fn next_key(&self, wtxn: &mut heed::RwTxn) -> Result<KeyId> {
        if self.meta.get(wtxn, RECOVERING_KEY)?.is_some() {
            return Err(Error::Recovering);
        }
        let next = match self.meta.get(wtxn, NEXT_INDEX_KEY)? {
            Some(b) => u32::from_le_bytes(b.try_into().map_err(|_| Error::Corrupt("next index"))?),
            None => 0,
        };
        let following = next.checked_add(1).ok_or(Error::Corrupt("key index exhausted"))?;
        self.meta.put(wtxn, NEXT_INDEX_KEY, &following.to_le_bytes())?;
        Ok(KeyId::new(ACCOUNT, next))
    }

    fn put_output(&self, wtxn: &mut heed::RwTxn, output: &OwnedOutput) -> Result<()> {
        self.outputs.put(wtxn, &output.commitment, &output.to_bytes())?;
        Ok(())
    }

    fn get_output(&self, txn: &heed::RoTxn, commitment: &[u8; 32]) -> Result<Option<OwnedOutput>> {
        match self.outputs.get(txn, commitment)? {
            Some(bytes) => Ok(Some(OwnedOutput::from_bytes(*commitment, bytes).ok_or(Error::Corrupt("output"))?)),
            None => Ok(None),
        }
    }

    fn put_slate(&self, wtxn: &mut heed::RwTxn, record: &SlateRecord) -> Result<()> {
        self.slates.put(wtxn, &record.slate.id, &record.to_bytes())?;
        Ok(())
    }

    pub fn slate(&self, id: &[u8; 16]) -> Result<Option<SlateRecord>> {
        let rtxn = self.storage.read_txn()?;
        match self.slates.get(&rtxn, id)? {
            Some(bytes) => Ok(Some(SlateRecord::from_bytes(bytes).ok_or(Error::Corrupt("slate"))?)),
            None => Ok(None),
        }
    }

    /// Record a new expected output paying `amount` to a fresh key.
    fn expect_output(&self, wtxn: &mut heed::RwTxn, amount: u64, origin: Origin) -> Result<OwnedOutput> {
        let key = self.next_key(wtxn)?;
        let record = OwnedOutput {
            commitment: self.keychain.output(key, amount).commitment(),
            key,
            amount,
            origin,
            lock: Lock::Free,
            seen_height: None,
            spent: false,
        };
        self.put_output(wtxn, &record)?;
        Ok(record)
    }

    /// Every output the wallet owns or expects.
    pub fn outputs(&self) -> Result<Vec<OwnedOutput>> {
        let rtxn = self.storage.read_txn()?;
        let mut out = Vec::new();
        for item in self.outputs.iter(&rtxn)? {
            let (k, v) = item?;
            let commitment: [u8; 32] = k.try_into().map_err(|_| Error::Corrupt("output key"))?;
            out.push(OwnedOutput::from_bytes(commitment, v).ok_or(Error::Corrupt("output"))?);
        }
        Ok(out)
    }

    /// Bring every output's chain status up to date (see the module docs).
    /// Call after every change to the chain.
    ///
    /// Returns the commitments of outputs that just confirmed **without a
    /// valid recovery nonce**. Once signed, a nonce can't be altered (the
    /// signature and the block's proof cover it), but the sender of a
    /// slate payment signs it, and could have changed ours first. The
    /// funds are fine, but the seed alone can't find that output again:
    /// the wallet file is its only record until it's spent.
    pub fn refresh(&self, chain: &impl ChainView) -> Result<Vec<[u8; 32]>> {
        let mut unrecoverable = Vec::new();
        let tip = chain.tip_height();
        let mut wtxn = self.storage.write_txn()?;
        let records: Vec<OwnedOutput> = {
            let mut v = Vec::new();
            for item in self.outputs.iter(&wtxn)? {
                let (k, bytes) = item?;
                let commitment: [u8; 32] = k.try_into().map_err(|_| Error::Corrupt("output key"))?;
                v.push(OwnedOutput::from_bytes(commitment, bytes).ok_or(Error::Corrupt("output"))?);
            }
            v
        };
        for mut record in records {
            let before = record;
            let signed = matches!(record.lock, Lock::Signed(_));
            if chain.is_unspent(&record.commitment) {
                record.spent = false;
                if record.seen_height.is_none() {
                    let on_chain = chain.output_record(&record.commitment);
                    record.seen_height = Some(on_chain.map_or(tip, |(height, _)| height));
                    if let Some((_, nonce)) = on_chain {
                        let found = recovery::identify(&self.keychain, &self.view_key, record.key.account, &record.commitment, &nonce);
                        if found != Some((record.key, record.amount)) {
                            unrecoverable.push(record.commitment);
                        }
                    }
                }
            } else if let Some((height, _)) = chain.output_record(&record.commitment) {
                // On chain once, gone from the unspent set: spent -- by us,
                // or by a copy of this wallet, or a spend signed before a
                // restore.
                record.spent = true;
                record.seen_height = Some(height);
            } else if signed {
                record.spent = true;
            } else {
                record.seen_height = None;
            }
            if record != before {
                self.put_output(&mut wtxn, &record)?;
            }
        }
        wtxn.commit()?;
        Ok(unrecoverable)
    }

    pub fn balance(&self, tip_height: u64) -> Result<Balance> {
        let mut b = Balance::default();
        for o in self.outputs()? {
            match o.status(tip_height) {
                Status::Confirmed { mature: true, .. } => b.spendable += o.amount,
                Status::Confirmed { mature: false, .. } => b.immature += o.amount,
                // A reward not on chain is a block still being mined (or
                // one that lost a race): not money yet.
                Status::Pending if o.origin == Origin::Mined => {}
                Status::Pending => b.pending += o.amount,
                Status::Locked | Status::Spending => b.locked += o.amount,
                Status::Spent => {}
                Status::Held { until, .. } => {
                    b.held += o.amount;
                    b.held_until = b.held_until.max(until);
                }
            }
        }
        Ok(b)
    }

    // ---- mining ---------------------------------------------------------

    /// An output for a block reward of `amount`, to a fresh key, recorded
    /// as expected.
    pub fn reward_output(&self, amount: u64) -> Result<(KeyId, Output)> {
        let mut wtxn = self.storage.write_txn()?;
        let record = self.expect_output(&mut wtxn, amount, Origin::Mined)?;
        wtxn.commit()?;
        Ok((record.key, self.sealed_output(record.key, amount)))
    }

    /// Drop an expected output that will never appear (a block template
    /// abandoned before it was mined). Only outputs never seen on chain
    /// and never locked are dropped.
    pub fn forget(&self, commitment: &[u8; 32]) -> Result<bool> {
        let mut wtxn = self.storage.write_txn()?;
        let forgettable = self
            .get_output(&wtxn, commitment)?
            .is_some_and(|o| o.lock == Lock::Free && o.seen_height.is_none());
        if forgettable {
            self.outputs.delete(&mut wtxn, commitment)?;
        }
        wtxn.commit()?;
        Ok(forgettable)
    }

    // ---- spending -------------------------------------------------------

    /// Spendable outputs covering `needed`: largest first, so the fewest
    /// inputs (each ~4 KB and ~13 s of the miner's proving), at most
    /// `MAX_INPUTS`. Returns them and their total.
    fn select(&self, needed: u64, tip_height: u64) -> Result<(Vec<OwnedOutput>, u64)> {
        let mut spendable: Vec<OwnedOutput> = self
            .outputs()?
            .into_iter()
            .filter(|o| matches!(o.status(tip_height), Status::Confirmed { mature: true, .. }))
            .collect();
        spendable.sort_by(|a, b| b.amount.cmp(&a.amount).then(a.commitment.cmp(&b.commitment)));
        let mut chosen = Vec::new();
        let mut total = 0u64;
        for o in spendable.iter().take(MAX_INPUTS) {
            if total >= needed {
                break;
            }
            total += o.amount;
            chosen.push(*o);
        }
        if total < needed {
            let reachable = spendable.iter().take(MAX_INPUTS).map(|o| o.amount).sum();
            return Err(Error::InsufficientFunds { spendable: reachable, needed });
        }
        Ok((chosen, total))
    }

    /// Move funds between this wallet's own keys: one transaction paying
    /// each of `amounts` to a fresh key, the rest (less `fee`) to change.
    /// Spends `inputs` (commitments of spendable outputs we own) if given,
    /// else chooses (`select`). Signed and stored before it's returned --
    /// submit it like a finalized payment. Splitting one output into
    /// several, or consolidating several into one, are both this.
    pub fn self_transfer(&self, inputs: Option<&[[u8; 32]]>, amounts: &[u64], fee: u64, tip_height: u64) -> Result<Transaction> {
        if amounts.is_empty() || amounts.contains(&0) {
            return Err(Error::WrongSlateState("pay at least one nonzero amount"));
        }
        let needed = amounts
            .iter()
            .try_fold(fee, |a, &v| a.checked_add(v))
            .ok_or(Error::InsufficientFunds { spendable: 0, needed: u64::MAX })?;
        let (chosen, total) = match inputs {
            None => self.select(needed, tip_height)?,
            Some(commitments) => {
                let rtxn = self.storage.read_txn()?;
                let mut chosen = Vec::new();
                for c in commitments {
                    let o = self.get_output(&rtxn, c)?.ok_or(Error::WrongSlateState("not one of this wallet's outputs"))?;
                    if !matches!(o.status(tip_height), Status::Confirmed { mature: true, .. }) || chosen.contains(&o) {
                        return Err(Error::WrongSlateState("an input isn't spendable"));
                    }
                    chosen.push(o);
                }
                if chosen.len() > MAX_INPUTS {
                    return Err(Error::WrongSlateState("too many inputs for one transaction"));
                }
                let total = chosen.iter().map(|o| o.amount).sum::<u64>();
                if total < needed {
                    return Err(Error::InsufficientFunds { spendable: total, needed });
                }
                (chosen, total)
            }
        };

        let mut wtxn = self.storage.write_txn()?;
        let mut outputs = Vec::new();
        for &amount in amounts.iter().chain(Some(total - needed).filter(|&c| c > 0).as_ref()) {
            outputs.push(self.expect_output(&mut wtxn, amount, Origin::Change)?);
        }
        let mut tx = Transaction::new();
        for o in &chosen {
            tx.add_input(&self.keychain.public_key(o.key), o.amount).map_err(|_| Error::Corrupt("transaction"))?;
        }
        for o in &outputs {
            tx.add_output(self.sealed_output(o.key, o.amount)).map_err(|_| Error::Corrupt("transaction"))?;
        }
        for o in &chosen {
            let (sk, pk) = self.keychain.derive(o.key);
            if !tx.sign_input(&pk, &sk) {
                return Err(Error::Slate(slate::Error::SigningFailed));
            }
        }
        if !tx.verify() {
            return Err(Error::Slate(slate::Error::SigningFailed));
        }
        // Stored, and the inputs marked as signed away, before anyone sees
        // the signatures.
        let id = tx.id();
        let lock: [u8; 16] = id[..16].try_into().unwrap();
        for mut o in chosen {
            o.lock = Lock::Signed(lock);
            self.put_output(&mut wtxn, &o)?;
        }
        self.transactions.put(&mut wtxn, &id, &tx.to_bytes())?;
        wtxn.commit()?;
        Ok(tx)
    }

    // ---- slates ---------------------------------------------------------

    /// Start paying `amount` (plus `fee`): pick spendable outputs, make the
    /// change output, lock the inputs, and return slate S1 for the
    /// receiver.
    pub fn send(&self, amount: u64, fee: u64, tip_height: u64) -> Result<Slate> {
        let needed = amount.checked_add(fee).ok_or(Error::InsufficientFunds { spendable: 0, needed: u64::MAX })?;
        let (chosen, total) = self.select(needed, tip_height)?;

        let mut wtxn = self.storage.write_txn()?;
        let change_amount = total - needed;
        let change = if change_amount > 0 {
            Some(self.expect_output(&mut wtxn, change_amount, Origin::Change)?)
        } else {
            None
        };
        let inputs = chosen.iter().map(|o| (self.keychain.public_key(o.key), o.amount)).collect();
        let change_outputs = change.iter().map(|c| self.sealed_output(c.key, c.amount)).collect();
        let slate = Slate::send(amount, fee, inputs, change_outputs)?;
        for mut o in chosen {
            o.lock = Lock::Locked(slate.id);
            self.put_output(&mut wtxn, &o)?;
        }
        self.put_slate(
            &mut wtxn,
            &SlateRecord {
                role: Role::Sender,
                state: SlateState::Sent,
                slate: slate.clone(),
                transaction: None,
            },
        )?;
        wtxn.commit()?;
        Ok(slate)
    }

    /// Receive a payment: add our output to `s1` and return slate S2 for
    /// the sender. Receiving the same slate again returns the same S2.
    pub fn receive(&self, s1: &Slate) -> Result<Slate> {
        if let Some(record) = self.slate(&s1.id)? {
            return match record.role {
                Role::Receiver => Ok(record.slate),
                Role::Sender => Err(Error::WrongSlateState("that's our own slate -- give it to the receiver")),
            };
        }
        let mut wtxn = self.storage.write_txn()?;
        let record = self.expect_output(&mut wtxn, s1.amount, Origin::Received)?;
        let s2 = s1.receive(self.sealed_output(record.key, s1.amount))?;
        self.put_slate(
            &mut wtxn,
            &SlateRecord {
                role: Role::Receiver,
                state: SlateState::Received,
                slate: s2.clone(),
                transaction: None,
            },
        )?;
        wtxn.commit()?;
        Ok(s2)
    }

    /// Finish a payment we started: check `s2` against our S1, sign, and
    /// return the transaction to submit -- stored first, and returned
    /// again (never re-signed) if this is called again.
    pub fn finalize(&self, s2: &Slate) -> Result<Transaction> {
        let record = self.slate(&s2.id)?.ok_or(Error::UnknownSlate)?;
        if record.role != Role::Sender {
            return Err(Error::WrongSlateState("only the sender finalizes"));
        }
        match record.state {
            SlateState::Finalized => {
                let tx = record.transaction.ok_or(Error::Corrupt("finalized slate without a transaction"))?;
                let theirs = record.slate.check_response(s2)?;
                return if tx.outputs.contains(&theirs) { Ok(tx) } else { Err(Error::AlreadyFinalized) };
            }
            SlateState::Cancelled => return Err(Error::WrongSlateState("that slate was cancelled")),
            SlateState::Sent => {}
            SlateState::Received => return Err(Error::Corrupt("sender slate in receiver state")),
        }
        record.slate.check_response(s2)?;

        // Our inputs' keys, by public key.
        let rtxn = self.storage.read_txn()?;
        let mut keys = Vec::new();
        for (pubkey, amount) in &record.slate.inputs {
            let commitment = Output::new(pubkey, *amount).commitment();
            let owned = self.get_output(&rtxn, &commitment)?.ok_or(Error::Corrupt("slate input not in wallet"))?;
            if owned.lock != Lock::Locked(record.slate.id) {
                return Err(Error::Corrupt("slate input not locked to it"));
            }
            keys.push((pubkey.clone(), owned));
        }
        drop(rtxn);
        let tx = s2.finalize(|pk| keys.iter().find(|(k, _)| k == pk).map(|(_, o)| self.keychain.secret_key(o.key)))?;

        // Persist before anyone sees the signature.
        let mut wtxn = self.storage.write_txn()?;
        for (_, mut owned) in keys {
            owned.lock = Lock::Signed(record.slate.id);
            self.put_output(&mut wtxn, &owned)?;
        }
        self.put_slate(
            &mut wtxn,
            &SlateRecord {
                state: SlateState::Finalized,
                transaction: Some(tx.clone()),
                ..record
            },
        )?;
        wtxn.commit()?;
        Ok(tx)
    }

    /// Abandon a payment we started but haven't finalized: free its
    /// inputs and drop its change. Safe because nothing was signed.
    pub fn cancel(&self, id: &[u8; 16]) -> Result<()> {
        let record = self.slate(id)?.ok_or(Error::UnknownSlate)?;
        if record.role != Role::Sender || record.state != SlateState::Sent {
            return Err(Error::WrongSlateState("only an unfinalized slate we sent can be cancelled"));
        }
        let mut wtxn = self.storage.write_txn()?;
        for (pubkey, amount) in &record.slate.inputs {
            let commitment = Output::new(pubkey, *amount).commitment();
            if let Some(mut owned) = self.get_output(&wtxn, &commitment)?
                && owned.lock == Lock::Locked(*id)
            {
                owned.lock = Lock::Free;
                self.put_output(&mut wtxn, &owned)?;
            }
        }
        for change in &record.slate.outputs {
            self.outputs.delete(&mut wtxn, &change.commitment())?;
        }
        self.put_slate(
            &mut wtxn,
            &SlateRecord {
                state: SlateState::Cancelled,
                ..record
            },
        )?;
        wtxn.commit()?;
        Ok(())
    }

    /// Every slate the wallet is part of.
    pub fn slates(&self) -> Result<Vec<SlateRecord>> {
        let rtxn = self.storage.read_txn()?;
        let mut out = Vec::new();
        for item in self.slates.iter(&rtxn)? {
            let (_, bytes) = item?;
            out.push(SlateRecord::from_bytes(bytes).ok_or(Error::Corrupt("slate"))?);
        }
        Ok(out)
    }

    /// Signed transactions not yet confirmed -- to (re)submit.
    pub fn unconfirmed_transactions(&self) -> Result<Vec<Transaction>> {
        let rtxn = self.storage.read_txn()?;
        let mut signed = Vec::new();
        for item in self.slates.iter(&rtxn)? {
            let (_, bytes) = item?;
            let record = SlateRecord::from_bytes(bytes).ok_or(Error::Corrupt("slate"))?;
            signed.extend(record.transaction);
        }
        for item in self.transactions.iter(&rtxn)? {
            let (_, bytes) = item?;
            signed.push(Transaction::from_bytes(bytes).ok_or(Error::Corrupt("transaction"))?);
        }
        let pending = |tx: &Transaction| {
            tx.inputs.iter().any(|i| {
                let c = Output::new(&i.pubkey, i.amount).commitment();
                self.get_output(&rtxn, &c).ok().flatten().is_some_and(|o| !o.spent)
            })
        };
        Ok(signed.into_iter().filter(|tx| pending(tx)).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prover::REWARD;
    use std::cell::RefCell;
    use std::collections::HashSet;

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            TempDir(std::env::temp_dir().join(format!("wallet-test-{}-{name}-{n}", std::process::id())))
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// A stand-in chain: a set of unspent commitments, a height, and
    /// (for outputs mined from real `Output`s) each one's height and
    /// nonce, as the real chain's output index keeps them.
    #[derive(Default)]
    struct FakeChain {
        /// Pretend to be fast-synced: no spent history.
        partial: bool,
        unspent: RefCell<HashSet<[u8; 32]>>,
        height: RefCell<u64>,
        records: RefCell<std::collections::HashMap<[u8; 32], OnChain>>,
    }

    /// An output's height and nonce, as `ChainView::output_record` gives.
    type OnChain = (u64, [u8; NONCE_LEN]);

    impl FakeChain {
        /// A block: spends `inputs`, creates `outputs`.
        fn mine(&self, inputs: &[[u8; 32]], outputs: &[[u8; 32]]) {
            let mut set = self.unspent.borrow_mut();
            for i in inputs {
                assert!(set.remove(i), "spending a missing output");
            }
            set.extend(outputs);
            *self.height.borrow_mut() += 1;
        }

        fn mine_tx(&self, tx: &Transaction) {
            let inputs: Vec<_> = tx.inputs.iter().map(|i| Output::new(&i.pubkey, i.amount).commitment()).collect();
            self.mine_outputs(&inputs, &tx.outputs);
        }

        /// A block creating these outputs, recording their nonces.
        fn mine_outputs(&self, inputs: &[[u8; 32]], outputs: &[Output]) {
            let commitments: Vec<_> = outputs.iter().map(|o| o.commitment()).collect();
            self.mine(inputs, &commitments);
            let height = *self.height.borrow();
            for o in outputs {
                self.records.borrow_mut().insert(o.commitment(), (height, o.nonce));
            }
        }

        fn empty_blocks(&self, n: u64) {
            *self.height.borrow_mut() += n;
        }
    }

    impl ChainView for FakeChain {
        fn tip_height(&self) -> u64 {
            *self.height.borrow()
        }
        fn is_unspent(&self, commitment: &[u8; 32]) -> bool {
            self.unspent.borrow().contains(commitment)
        }
        fn output_record(&self, commitment: &[u8; 32]) -> Option<(u64, [u8; NONCE_LEN])> {
            self.records.borrow().get(commitment).copied()
        }
        fn has_full_history(&self) -> bool {
            !self.partial
        }
        fn for_each_output(&self, f: &mut dyn FnMut([u8; 32], u64, [u8; NONCE_LEN], bool)) -> bool {
            for (c, &(height, nonce)) in self.records.borrow().iter() {
                // Without history, only unspent outputs are known.
                if self.is_unspent(c) || !self.partial {
                    f(*c, height, nonce, self.is_unspent(c));
                }
            }
            true
        }
    }

    fn open(dir: &TempDir, label: &str) -> Wallet {
        Wallet::open_with(&dir.0, Keychain::test(label)).unwrap()
    }

    /// A wallet with `rewards` mined and matured.
    fn funded(dir: &TempDir, label: &str, chain: &FakeChain, rewards: &[u64]) -> Wallet {
        let w = open(dir, label);
        for &r in rewards {
            let (_, output) = w.reward_output(r).unwrap();
            chain.mine_outputs(&[], &[output]);
            assert!(w.refresh(chain).unwrap().is_empty()); // as a node does after every block
        }
        chain.empty_blocks(COINBASE_MATURITY);
        w.refresh(chain).unwrap();
        w
    }

    #[test]
    fn a_new_wallet_keeps_its_seed_and_never_reuses_a_key() {
        let dir = TempDir::new("seed");
        let first = Wallet::open(&dir.0).unwrap();
        let seed = *first.keychain().seed();
        let (k0, _) = first.reward_output(1).unwrap();
        let (k1, _) = first.reward_output(1).unwrap();
        drop(first);
        let again = Wallet::open(&dir.0).unwrap();
        assert_eq!(again.keychain().seed(), &seed);
        let (k2, _) = again.reward_output(1).unwrap();
        assert_eq!((k0.index, k1.index, k2.index), (0, 1, 2));
        // Restoring into it with a different seed is refused.
        drop(again);
        assert!(matches!(Wallet::open_with(&dir.0, Keychain::test("other")), Err(Error::Corrupt(_))));
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(std::fs::metadata(&dir.0).unwrap().permissions().mode() & 0o777, 0o700);
        }
    }

    #[test]
    fn rewards_go_pending_confirmed_mature() {
        let dir = TempDir::new("rewards");
        let chain = FakeChain::default();
        let w = open(&dir, "rewards");
        let (_, output) = w.reward_output(REWARD).unwrap();
        assert_eq!(w.balance(0).unwrap(), Balance::default(), "a block being mined isn't money yet");
        chain.mine(&[], &[output.commitment()]);
        w.refresh(&chain).unwrap();
        assert_eq!(w.balance(chain.tip_height()).unwrap().immature, REWARD);
        chain.empty_blocks(COINBASE_MATURITY - 1);
        w.refresh(&chain).unwrap();
        assert_eq!(w.balance(chain.tip_height()).unwrap().spendable, REWARD);
        // A template that was never mined.
        let (_, abandoned) = w.reward_output(REWARD).unwrap();
        assert!(w.forget(&abandoned.commitment()).unwrap());
        assert!(!w.forget(&output.commitment()).unwrap(), "a confirmed output isn't forgotten");
        assert_eq!(w.outputs().unwrap().len(), 1);
    }

    /// Alice pays Bob through slates; the transaction confirms; both
    /// wallets agree.
    #[test]
    fn a_payment_between_two_wallets() {
        let (da, db) = (TempDir::new("alice"), TempDir::new("bob"));
        let chain = FakeChain::default();
        let alice = funded(&da, "alice", &chain, &[REWARD, REWARD]);
        let bob = open(&db, "bob");
        let tip = chain.tip_height();
        assert_eq!(alice.balance(tip).unwrap().spendable, 2 * REWARD);

        let amount = REWARD + REWARD / 2;
        let fee = 1_000;
        let s1 = alice.send(amount, fee, tip).unwrap();
        assert_eq!(s1.inputs.len(), 2);
        assert_eq!(
            alice.balance(tip).unwrap(),
            Balance {
                spendable: 0,
                immature: 0,
                pending: REWARD / 2 - fee,
                locked: 2 * REWARD,
                ..Default::default()
            }
        );

        let s2 = bob.receive(&s1).unwrap();
        assert_eq!(bob.balance(tip).unwrap().pending, amount);
        // Receiving the same slate again doesn't make a second output.
        assert_eq!(bob.receive(&s1).unwrap(), s2);
        assert_eq!(bob.outputs().unwrap().len(), 1);

        let tx = alice.finalize(&s2).unwrap();
        assert!(tx.verify());
        assert_eq!(tx.fee(), Some(fee));
        // Finalizing again returns the very same transaction.
        assert_eq!(alice.finalize(&s2).unwrap().to_bytes(), tx.to_bytes());
        assert_eq!(alice.unconfirmed_transactions().unwrap().len(), 1);

        chain.mine_tx(&tx);
        alice.refresh(&chain).unwrap();
        bob.refresh(&chain).unwrap();
        let tip = chain.tip_height();
        assert_eq!(alice.balance(tip).unwrap(), Balance { spendable: REWARD / 2 - fee, ..Default::default() });
        assert_eq!(bob.balance(tip).unwrap(), Balance { spendable: amount, ..Default::default() });
        assert!(alice.unconfirmed_transactions().unwrap().is_empty());
        let statuses: Vec<Status> = alice.outputs().unwrap().iter().map(|o| o.status(tip)).collect();
        assert_eq!(statuses.iter().filter(|s| **s == Status::Spent).count(), 2);
    }

    #[test]
    fn a_finalized_slate_is_never_signed_again() {
        let (da, db, dc) = (TempDir::new("a"), TempDir::new("b"), TempDir::new("c"));
        let chain = FakeChain::default();
        let alice = funded(&da, "alice2", &chain, &[REWARD]);
        let s1 = alice.send(100, 1, chain.tip_height()).unwrap();
        let s2 = open(&db, "bob2").receive(&s1).unwrap();
        alice.finalize(&s2).unwrap();
        // A second receiver answering the same S1 gets nothing signed.
        let other = open(&dc, "carol2").receive(&s1).unwrap();
        assert!(matches!(alice.finalize(&other), Err(Error::AlreadyFinalized)));
        assert!(matches!(alice.cancel(&s1.id), Err(Error::WrongSlateState(_))));
    }

    #[test]
    fn cancelling_frees_the_inputs_and_drops_the_change() {
        let da = TempDir::new("cancel");
        let chain = FakeChain::default();
        let alice = funded(&da, "alice3", &chain, &[REWARD]);
        let tip = chain.tip_height();
        let s1 = alice.send(100, 1, tip).unwrap();
        assert_eq!(alice.balance(tip).unwrap().spendable, 0);
        alice.cancel(&s1.id).unwrap();
        assert_eq!(alice.balance(tip).unwrap(), Balance { spendable: REWARD, ..Default::default() });
        assert_eq!(alice.outputs().unwrap().len(), 1);
        // A cancelled slate can't then be finalized.
        let db = TempDir::new("cancel-bob");
        let s2 = open(&db, "bob3").receive(&s1).unwrap();
        assert!(matches!(alice.finalize(&s2), Err(Error::WrongSlateState(_))));
    }

    #[test]
    fn a_tampered_response_signs_nothing_and_locks_nothing_new() {
        let (da, db) = (TempDir::new("tamper"), TempDir::new("tamper-bob"));
        let chain = FakeChain::default();
        let alice = funded(&da, "alice4", &chain, &[REWARD]);
        let s1 = alice.send(100, 1, chain.tip_height()).unwrap();
        let mut s2 = open(&db, "bob4").receive(&s1).unwrap();
        s2.outputs[0] = Keychain::test("bob4").output(KeyId::new(0, 9), s2.outputs[0].amount);
        assert!(matches!(alice.finalize(&s2), Err(Error::Slate(slate::Error::Tampered(_)))));
        assert!(alice.outputs().unwrap().iter().all(|o| !matches!(o.lock, Lock::Signed(_))));
        assert!(alice.slate(&s1.id).unwrap().unwrap().transaction.is_none());
    }

    #[test]
    fn coin_selection_limits() {
        let da = TempDir::new("select");
        let chain = FakeChain::default();
        // Twelve small outputs: only eight (a chunk's inputs) may be spent
        // at once.
        let alice = funded(&da, "alice5", &chain, &[100; 12]);
        let tip = chain.tip_height();
        assert!(matches!(
            alice.send(850, 0, tip),
            Err(Error::InsufficientFunds { spendable: 800, needed: 850 })
        ));
        let s1 = alice.send(750, 10, tip).unwrap();
        assert_eq!(s1.inputs.len(), 8);
        // Immature rewards don't count.
        let db = TempDir::new("select-young");
        let young = open(&db, "young");
        let (_, o) = young.reward_output(REWARD).unwrap();
        chain.mine(&[], &[o.commitment()]);
        young.refresh(&chain).unwrap();
        assert!(matches!(young.send(1, 0, chain.tip_height()), Err(Error::InsufficientFunds { .. })));
    }

    /// A reorg that removes a confirmed output, then brings it back.
    #[test]
    fn reorgs_unconfirm_and_reconfirm() {
        let da = TempDir::new("reorg");
        let chain = FakeChain::default();
        let alice = funded(&da, "alice6", &chain, &[REWARD]);
        let commitment = alice.outputs().unwrap()[0].commitment;
        // Its block is unwound: gone from the unspent set and the output
        // index both.
        chain.unspent.borrow_mut().remove(&commitment);
        let record = chain.records.borrow_mut().remove(&commitment).unwrap();
        alice.refresh(&chain).unwrap();
        assert_eq!(alice.balance(chain.tip_height()).unwrap(), Balance::default());
        assert_eq!(alice.outputs().unwrap()[0].status(chain.tip_height()), Status::Pending);
        chain.unspent.borrow_mut().insert(commitment);
        chain.records.borrow_mut().insert(commitment, record);
        alice.refresh(&chain).unwrap();
        chain.empty_blocks(COINBASE_MATURITY);
        alice.refresh(&chain).unwrap();
        assert_eq!(alice.balance(chain.tip_height()).unwrap().spendable, REWARD);
    }

    #[test]
    fn self_transfers_split_and_consolidate() {
        let da = TempDir::new("self");
        let chain = FakeChain::default();
        let alice = funded(&da, "alice7", &chain, &[REWARD]);
        let tip = chain.tip_height();
        // Split one reward into four, fee 100.
        let split = alice.self_transfer(None, &[1_000; 4], 100, tip).unwrap();
        assert!(split.verify());
        assert_eq!((split.inputs.len(), split.outputs.len(), split.fee()), (1, 5, Some(100)));
        assert_eq!(alice.unconfirmed_transactions().unwrap().len(), 1);
        assert_eq!(alice.balance(tip).unwrap().spendable, 0, "its input is signed away");
        chain.mine_tx(&split);
        alice.refresh(&chain).unwrap();
        let tip = chain.tip_height();
        assert_eq!(alice.balance(tip).unwrap(), Balance { spendable: REWARD - 100, ..Default::default() });
        assert!(alice.unconfirmed_transactions().unwrap().is_empty());
        // Consolidate exactly the three of the small ones we name.
        let small: Vec<[u8; 32]> = alice.outputs().unwrap().iter().filter(|o| o.amount == 1_000).map(|o| o.commitment).take(3).collect();
        let merged = alice.self_transfer(Some(&small), &[2_990], 10, tip).unwrap();
        assert_eq!((merged.inputs.len(), merged.outputs.len()), (3, 1));
        // Named inputs must be ours and spendable.
        assert!(alice.self_transfer(Some(&small[..1]), &[1], 0, tip).is_err(), "already signed away");
        assert!(alice.self_transfer(Some(&[[9; 32]]), &[1], 0, tip).is_err());
        assert!(matches!(alice.self_transfer(None, &[REWARD * 2], 0, tip), Err(Error::InsufficientFunds { .. })));
    }

    /// Every kind of output the wallet creates -- reward, change,
    /// received payment, self-transfer -- carries a nonce its owner's
    /// seed can read back; and refresh accepts them all.
    #[test]
    fn every_output_the_wallet_makes_is_recoverable() {
        let (da, db) = (TempDir::new("seal-a"), TempDir::new("seal-b"));
        let chain = FakeChain::default();
        let alice = funded(&da, "seal alice", &chain, &[REWARD, REWARD]);
        let bob = open(&db, "seal bob");
        let tip = chain.tip_height();
        let s1 = alice.send(REWARD / 2, 100, tip).unwrap();
        let s2 = bob.receive(&s1).unwrap();
        let payment = alice.finalize(&s2).unwrap();
        let split = alice.self_transfer(None, &[1_000, 2_000], 50, tip).unwrap();
        for tx in [&payment, &split] {
            chain.mine_tx(tx);
            assert!(alice.refresh(&chain).unwrap().is_empty());
            assert!(bob.refresh(&chain).unwrap().is_empty());
        }
        let readable = |w: &Wallet, o: &OwnedOutput| {
            let (_, nonce) = chain.output_record(&o.commitment).unwrap();
            let k = Keychain::from_seed(*w.keychain().seed());
            recovery::identify(&k, &k.view_key(), o.key.account, &o.commitment, &nonce) == Some((o.key, o.amount))
        };
        let mut checked = 0;
        for (w, outputs) in [(&alice, alice.outputs().unwrap()), (&bob, bob.outputs().unwrap())] {
            for o in outputs.iter().filter(|o| chain.output_record(&o.commitment).is_some()) {
                assert!(readable(w, o), "{:?} output", o.origin);
                checked += 1;
            }
        }
        // Two rewards; payment: Bob's output, Alice's change; split: two
        // pieces and change.
        assert_eq!(checked, 7);
        assert!(bob.outputs().unwrap().iter().any(|o| o.origin == Origin::Received && readable(&bob, o)));
    }

    /// A nonce altered on the way to the chain is reported when its
    /// output confirms (once), and the output still counts as ours.
    #[test]
    fn an_altered_nonce_is_reported_at_confirmation() {
        let da = TempDir::new("tamper");
        let chain = FakeChain::default();
        let alice = funded(&da, "tamper alice", &chain, &[REWARD]);
        let tip = chain.tip_height();
        let mut tx = alice.self_transfer(None, &[1_000], 10, tip).unwrap();
        // A relay flips a bit in one output's nonce (nothing signs it).
        tx.outputs[0].nonce[0] ^= 1;
        let altered = tx.outputs[0].commitment();
        chain.mine_tx(&tx);
        assert_eq!(alice.refresh(&chain).unwrap(), vec![altered]);
        assert!(alice.refresh(&chain).unwrap().is_empty(), "reported once");
        assert_eq!(alice.balance(chain.tip_height()).unwrap().pending, 0);
    }

    /// Confirmations count from the block that created the output, even
    /// when the wallet first looks much later.
    #[test]
    fn confirmations_count_from_the_including_block() {
        let da = TempDir::new("height");
        let chain = FakeChain::default();
        let alice = open(&da, "height alice");
        let (_, reward) = alice.reward_output(REWARD).unwrap();
        chain.mine_outputs(&[], &[reward]);
        let mined_at = chain.tip_height();
        chain.empty_blocks(COINBASE_MATURITY); // the wallet was offline
        alice.refresh(&chain).unwrap();
        let o = alice.outputs().unwrap()[0];
        assert_eq!(o.seen_height, Some(mined_at));
        assert_eq!(alice.balance(chain.tip_height()).unwrap().spendable, REWARD, "already mature");
    }

    /// The unspent outputs a wallet holds, as (commitment, amount).
    fn unspent_set(w: &Wallet) -> Vec<([u8; 32], u64)> {
        let mut v: Vec<_> = w.outputs().unwrap().iter().filter(|o| o.seen_height.is_some() && !o.spent).map(|o| (o.commitment, o.amount)).collect();
        v.sort();
        v
    }

    /// The acceptance test in miniature: a wallet that mined, paid,
    /// received, split and made change is lost; one restored from its
    /// seed alone ends up with exactly the same unspent outputs, knows
    /// which ones were spent, never reuses a key, and can spend after
    /// the hold.
    #[test]
    fn a_wallet_restored_from_its_seed_finds_everything() {
        let (da, db, dr) = (TempDir::new("lost"), TempDir::new("payer"), TempDir::new("restored"));
        let chain = FakeChain::default();
        let lost = funded(&da, "recover me", &chain, &[REWARD, REWARD, REWARD]);
        let bob = funded(&db, "recover bob", &chain, &[REWARD]);
        let tip = chain.tip_height();
        // Pay Bob (spends a reward, makes change); receive from Bob;
        // split a reward.
        let s1 = lost.send(REWARD / 3, 100, tip).unwrap();
        chain.mine_tx(&lost.finalize(&bob.receive(&s1).unwrap()).unwrap());
        let s1 = bob.send(REWARD / 5, 100, chain.tip_height()).unwrap();
        chain.mine_tx(&bob.finalize(&lost.receive(&s1).unwrap()).unwrap());
        lost.refresh(&chain).unwrap();
        chain.mine_tx(&lost.self_transfer(None, &[7_000, 8_000], 10, chain.tip_height()).unwrap());
        lost.refresh(&chain).unwrap();
        chain.empty_blocks(COINBASE_MATURITY);
        lost.refresh(&chain).unwrap();
        let used = lost.outputs().unwrap().iter().map(|o| o.key.index).max().unwrap();
        let before = lost.balance(chain.tip_height()).unwrap();
        let expected = unspent_set(&lost);
        assert!(expected.len() >= 5);
        let seed = *lost.keychain().seed();
        drop(lost);

        // Restore from the words alone.
        let words = Keychain::from_seed(seed).phrase();
        let restored = Wallet::restore(&dr.0, Keychain::from_phrase(&words).unwrap()).unwrap();
        assert!(restored.is_recovering().unwrap());
        assert!(matches!(restored.reward_output(1), Err(Error::Recovering)), "no keys before the scan");
        let report = restored.finish_recovery(&chain).unwrap();
        assert!(!restored.is_recovering().unwrap());
        assert_eq!((report.unspent, report.amount), (expected.len(), expected.iter().map(|e| e.1).sum()));
        assert!(report.outputs > report.unspent, "spent outputs are found too");
        assert!(report.next_index > used + RECOVERY_INDEX_MARGIN);
        assert_eq!(unspent_set(&restored), expected);

        // Held at first; spendable after the hold, with the same total.
        let tip = chain.tip_height();
        let held = restored.balance(tip).unwrap();
        assert_eq!((held.spendable, held.immature), (0, 0));
        assert_eq!((held.held, held.held_until), (before.spendable + before.immature, report.spendable_from));
        assert!(restored.outputs().unwrap().iter().filter(|o| !o.spent).all(|o| matches!(o.status(tip), Status::Held { until, .. } if until == report.spendable_from)));
        assert!(restored.send(1, 0, tip).is_err());
        chain.empty_blocks(RECOVERY_HOLD_BLOCKS);
        restored.refresh(&chain).unwrap();
        let after = restored.balance(chain.tip_height()).unwrap();
        assert_eq!(after.spendable, before.spendable + before.immature);
        // And it works: a new key well past every old one.
        let (key, _) = restored.reward_output(1).unwrap();
        assert_eq!(key.index, report.next_index);
        let tx = restored.self_transfer(None, &[1_000], 10, chain.tip_height()).unwrap();
        chain.mine_tx(&tx);
        assert!(restored.refresh(&chain).unwrap().is_empty());
    }

    /// A spend the lost wallet signed but that hadn't confirmed: once the
    /// restored wallet sees it (in the mempool), it never signs that
    /// output again, and resubmits the spend itself.
    #[test]
    fn a_restored_wallet_respects_a_spend_still_in_flight() {
        let (da, dr) = (TempDir::new("inflight"), TempDir::new("inflight-restored"));
        let chain = FakeChain::default();
        let lost = funded(&da, "inflight", &chain, &[REWARD]);
        let in_flight = lost.self_transfer(None, &[1_000], 10, chain.tip_height()).unwrap();
        let seed = *lost.keychain().seed();
        drop(lost);

        let restored = Wallet::restore(&dr.0, Keychain::from_seed(seed)).unwrap();
        restored.finish_recovery(&chain).unwrap();
        assert!(restored.observe_spend(&in_flight).unwrap());
        assert!(!restored.observe_spend(&in_flight).unwrap(), "already noted");
        let resubmit: Vec<_> = restored.unconfirmed_transactions().unwrap().iter().map(Transaction::id).collect();
        assert_eq!(resubmit, vec![in_flight.id()]);
        chain.empty_blocks(RECOVERY_HOLD_BLOCKS);
        restored.refresh(&chain).unwrap();
        assert!(restored.self_transfer(None, &[1], 0, chain.tip_height()).is_err(), "never signed twice");
        // It confirms: the recovered input reads as spent, and the
        // spend's outputs -- sealed to our seed -- are ours.
        chain.mine_tx(&in_flight);
        restored.refresh(&chain).unwrap();
        let outputs = restored.outputs().unwrap();
        let (spent, unspent): (Vec<&OwnedOutput>, Vec<&OwnedOutput>) = outputs.iter().partition(|o| o.spent);
        assert_eq!(spent.len(), 1);
        let mut found: Vec<_> = unspent.iter().map(|o| o.commitment).collect();
        let mut made: Vec<_> = in_flight.outputs.iter().map(|o| o.commitment()).collect();
        found.sort();
        made.sort();
        assert_eq!(found, made);
        assert!(unspent.iter().all(|o| o.seen_height.is_some()));
    }

    /// A passphrase wallet: its words alone restore a different (empty)
    /// wallet; words and passphrase restore it.
    #[test]
    fn a_passphrase_wallet_needs_words_and_passphrase() {
        let (d, wrong, right) = (TempDir::new("pp"), TempDir::new("pp-wrong"), TempDir::new("pp-right"));
        let chain = FakeChain::default();
        let w = Wallet::create_with_passphrase(&d.0, "hunter2 is not a good one").unwrap();
        let (words, passphrase) = w.backup_words().unwrap();
        assert!(passphrase);
        assert_ne!(Keychain::from_phrase(&words).unwrap().seed(), w.keychain().seed(), "the words alone aren't the seed");
        let (_, reward) = w.reward_output(REWARD).unwrap();
        chain.mine_outputs(&[], &[reward]);
        drop(w);

        let without = Wallet::restore_from_words(&wrong.0, &words, "").unwrap();
        assert_eq!(without.finish_recovery(&chain).unwrap().outputs, 0);
        let with = Wallet::restore_from_words(&right.0, &words, "hunter2 is not a good one").unwrap();
        assert_eq!(with.finish_recovery(&chain).unwrap().amount, REWARD);
        assert_eq!(with.backup_words().unwrap(), (words, true));
        // A wallet without one: the words are the seed, as always.
        let plain = open(&TempDir::new("pp-plain"), "plain");
        let (plain_words, pp) = plain.backup_words().unwrap();
        assert!(!pp);
        assert_eq!(Keychain::from_phrase(&plain_words).unwrap().seed(), plain.keychain().seed());
    }

    /// On a chain without spent history, recovery can't see a spent
    /// output's key -- possibly the highest ever used -- so it resumes
    /// keys far past what it does see.
    #[test]
    fn without_spent_history_recovery_leaves_a_wider_gap() {
        let (da, dr) = (TempDir::new("partial"), TempDir::new("partial-restored"));
        let mut chain = FakeChain::default();
        let lost = funded(&da, "partial", &chain, &[REWARD, REWARD]);
        // Spend the newest reward entirely (its key is the highest used).
        let newest = lost.outputs().unwrap().into_iter().max_by_key(|o| o.key.index).unwrap().commitment;
        chain.mine_tx(&lost.self_transfer(Some(&[newest]), &[REWARD - 10], 10, chain.tip_height()).unwrap());
        let used = lost.outputs().unwrap().iter().map(|o| o.key.index).max().unwrap();
        let seed = *lost.keychain().seed();
        drop(lost);
        chain.partial = true;
        let restored = Wallet::restore(&dr.0, Keychain::from_seed(seed)).unwrap();
        let report = restored.finish_recovery(&chain).unwrap();
        assert!(report.next_index >= RECOVERY_INDEX_MARGIN_WITHOUT_HISTORY);
        assert!(report.next_index > used + RECOVERY_INDEX_MARGIN);
    }

    #[test]
    fn restore_refuses_an_existing_wallet() {
        let d = TempDir::new("exists");
        drop(open(&d, "exists"));
        assert!(matches!(Wallet::restore(&d.0, Keychain::test("exists")), Err(Error::Exists)));
    }

    /// An output spent by someone else holding our keys (a copy of the
    /// wallet) reads as spent, not as vanished.
    #[test]
    fn an_output_spent_elsewhere_reads_as_spent() {
        let (da, db) = (TempDir::new("copy-a"), TempDir::new("copy-b"));
        let chain = FakeChain::default();
        let a = funded(&da, "copied", &chain, &[REWARD]);
        let b = Wallet::restore(&db.0, Keychain::from_seed(*a.keychain().seed())).unwrap();
        b.finish_recovery(&chain).unwrap();
        chain.empty_blocks(RECOVERY_HOLD_BLOCKS);
        b.refresh(&chain).unwrap();
        chain.mine_tx(&b.self_transfer(None, &[1_000], 10, chain.tip_height()).unwrap());
        a.refresh(&chain).unwrap();
        let reward = a.outputs().unwrap().into_iter().find(|o| o.origin == Origin::Mined).unwrap();
        assert_eq!(reward.status(chain.tip_height()), Status::Spent);
        assert_eq!(a.balance(chain.tip_height()).unwrap().spendable, 0);
    }

    #[test]
    fn records_round_trip() {
        let o = OwnedOutput {
            commitment: [7; 32],
            key: KeyId::new(0, 42),
            amount: 123,
            origin: Origin::Change,
            lock: Lock::Signed([9; 16]),
            seen_height: Some(77),
            spent: true,
        };
        assert_eq!(OwnedOutput::from_bytes(o.commitment, &o.to_bytes()), Some(o));
        let fresh = OwnedOutput { lock: Lock::Free, seen_height: None, spent: false, ..o };
        assert_eq!(OwnedOutput::from_bytes(o.commitment, &fresh.to_bytes()), Some(fresh));
    }
}

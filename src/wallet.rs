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

/// What the chain can tell the wallet.
pub trait ChainView {
    /// The active chain's height.
    fn tip_height(&self) -> u64;
    /// Whether `commitment` is an unspent output of the active chain.
    fn is_unspent(&self, commitment: &[u8; 32]) -> bool;
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
}

/// The wallet's own intent for an output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lock {
    Free,
    /// An input of this unfinished slate (cancelling frees it).
    Locked([u8; 16]),
    /// An input of this slate's signed transaction (permanent).
    Signed([u8; 16]),
}

/// An output the wallet owns (or expects to).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OwnedOutput {
    pub commitment: [u8; 32],
    pub key: KeyId,
    pub amount: u64,
    pub origin: Origin,
    pub lock: Lock,
    /// The chain height at which `refresh` first saw it unspent, while
    /// it's on chain. Confirmations count from here: a wallet refreshed
    /// after every block (as a node does) counts exactly; one that was
    /// offline counts fewer, which only errs on the safe side (rewards
    /// mature later, never earlier).
    pub seen_height: Option<u64>,
    /// Gone from the chain after we signed it away (`refresh`).
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
}

impl OwnedOutput {
    pub fn status(&self, tip_height: u64) -> Status {
        match (self.lock, self.seen_height, self.spent) {
            (Lock::Signed(_), _, true) => Status::Spent,
            (Lock::Signed(_), _, false) => Status::Spending,
            (Lock::Locked(_), _, _) => Status::Locked,
            (Lock::Free, None, _) => Status::Pending,
            (Lock::Free, Some(h), _) => {
                let confirmations = tip_height.saturating_sub(h) + 1;
                let mature = self.origin != Origin::Mined || confirmations >= COINBASE_MATURITY;
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
            _ => return None,
        };
        let id: [u8; 16] = bytes[18..34].try_into().unwrap();
        let lock = match bytes[17] {
            0 => Lock::Free,
            1 => Lock::Locked(id),
            2 => Lock::Signed(id),
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
}

pub struct Wallet {
    storage: Storage,
    keychain: Keychain,
    meta: Database<Bytes, Bytes>,
    outputs: Database<Bytes, Bytes>,
    slates: Database<Bytes, Bytes>,
    /// Signed transactions that aren't slates (`self_transfer`), by id.
    transactions: Database<Bytes, Bytes>,
}

impl Wallet {
    /// Open the wallet in `dir`, creating it -- with a new random seed --
    /// if it doesn't exist. The directory is made private to the user.
    pub fn open(dir: &Path) -> Result<Wallet> {
        Self::open_inner(dir, None)
    }

    /// Open the wallet in `dir`, creating it from `keychain`'s seed if it
    /// doesn't exist (restore, or tests). An existing wallet must have the
    /// same seed.
    pub fn open_with(dir: &Path, keychain: Keychain) -> Result<Wallet> {
        Self::open_inner(dir, Some(keychain))
    }

    fn open_inner(dir: &Path, keychain: Option<Keychain>) -> Result<Wallet> {
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
                keychain
            }
        };
        wtxn.commit()?;
        Ok(Wallet {
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

    /// Hand out the next unused key, recording that in `wtxn` -- committed
    /// together with whatever uses it, so a key is never handed out twice.
    fn next_key(&self, wtxn: &mut heed::RwTxn) -> Result<KeyId> {
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
    pub fn refresh(&self, chain: &impl ChainView) -> Result<()> {
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
                    record.seen_height = Some(tip);
                }
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
        Ok(())
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
        Ok((record.key, self.keychain.output(record.key, amount)))
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
            tx.add_output(self.keychain.output(o.key, o.amount)).map_err(|_| Error::Corrupt("transaction"))?;
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
        let change_outputs = change.iter().map(|c| self.keychain.output(c.key, c.amount)).collect();
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
        let s2 = s1.receive(self.keychain.output(record.key, s1.amount))?;
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

    /// A stand-in chain: a set of unspent commitments and a height.
    #[derive(Default)]
    struct FakeChain {
        unspent: RefCell<HashSet<[u8; 32]>>,
        height: RefCell<u64>,
    }

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
            let outputs: Vec<_> = tx.outputs.iter().map(|o| o.commitment()).collect();
            self.mine(&inputs, &outputs);
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
    }

    fn open(dir: &TempDir, label: &str) -> Wallet {
        Wallet::open_with(&dir.0, Keychain::test(label)).unwrap()
    }

    /// A wallet with `rewards` mined and matured.
    fn funded(dir: &TempDir, label: &str, chain: &FakeChain, rewards: &[u64]) -> Wallet {
        let w = open(dir, label);
        for &r in rewards {
            let (_, output) = w.reward_output(r).unwrap();
            chain.mine(&[], &[output.commitment()]);
            w.refresh(chain).unwrap(); // as a node does after every block
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
        // Twelve small outputs: only ten may be spent at once.
        let alice = funded(&da, "alice5", &chain, &[100; 12]);
        let tip = chain.tip_height();
        assert!(matches!(
            alice.send(1_050, 0, tip),
            Err(Error::InsufficientFunds { spendable: 1_000, needed: 1_050 })
        ));
        let s1 = alice.send(950, 10, tip).unwrap();
        assert_eq!(s1.inputs.len(), 10);
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
        chain.unspent.borrow_mut().remove(&commitment);
        alice.refresh(&chain).unwrap();
        assert_eq!(alice.balance(chain.tip_height()).unwrap(), Balance::default());
        assert_eq!(alice.outputs().unwrap()[0].status(chain.tip_height()), Status::Pending);
        chain.unspent.borrow_mut().insert(commitment);
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

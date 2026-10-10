//! The persistent table of known peer hosts, for `discovery`: every IPv4
//! `address:port` this node has heard of, with just enough state to tell
//! the ones actually known to answer from the ones merely claimed to
//! exist.
//!
//! A host enters as a *candidate* (heard about it -- from a `HOSTS`
//! reply, a configured seed, or because it queried us) and becomes
//! *verified* the first time it actually answers one of our requests;
//! `last_success_ms` is when it last did. Each request that goes
//! unanswered counts as a failure, and a success resets the count. Only
//! verified hosts with no outstanding failures are handed out to other
//! peers (`active`), so this node never repeats an address it hasn't
//! confirmed itself -- or one that's stopped answering.
//!
//! A host that stops answering is kept, and re-asked (by `discovery`), so
//! a node finds its peers again when they come back -- for a while:
//!
//! - one that has never answered is removed after `NEVER_ANSWERED_TRIES`
//!   unanswered requests (a made-up or mistyped address, or one planted
//!   by a lying peer, doesn't linger -- and isn't probed for ever);
//! - one that has answered, but not for `SILENT_DROP_MS` (a week), is
//!   removed: a node that comes back after that reaches out itself;
//! - `discovery` asks a host silent over a day only hourly.
//!
//! A `protect`ed host (a seed) is never removed, nor evicted: a node can
//! always find its way back to the network. At most `max_per_ip` hosts
//! share an IP address (so one address can't fill the table, or be sprayed
//! with probes on many ports). The table is bounded by `max_hosts`; once
//! full, a new host takes the place of the one silent longest among those
//! not answering now (never answered at all, first) -- never one that is
//! answering, and never a seed. So a flood of made-up addresses can only
//! displace each other and dead hosts, not the network this node is
//! talking to.
//!
//! Backed by LMDB via the shared `storage::Storage`, like everything
//! else that persists, so the table survives restarts: a node that has
//! run before doesn't need its seeds to find the network again.

#![allow(dead_code)]

use crate::storage::Storage;
use heed::Database;
use heed::types::Bytes;
use std::collections::HashSet;
use std::net::{Ipv4Addr, SocketAddrV4};

const PEERS_DB: &str = "peers";

/// Unanswered requests after which a host that has never answered is
/// removed.
pub const NEVER_ANSWERED_TRIES: u8 = 3;

/// How long a host that has answered may then go silent before it's
/// removed: a week, in milliseconds.
pub const SILENT_DROP_MS: u64 = 7 * 24 * 60 * 60 * 1000;

/// Encoded length of an address: 4 bytes of IPv4, 2 of port (big-endian).
pub const ADDR_LEN: usize = 6;

/// Encoded length of a `HostRecord`: `last_success_ms` (8) + `failures` (1).
const RECORD_LEN: usize = 9;

#[derive(Debug)]
pub enum Error {
    Storage(crate::storage::Error),
    Heed(heed::Error),
    Corrupt(&'static str),
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

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Storage(e) => write!(f, "storage error: {e}"),
            Error::Heed(e) => write!(f, "LMDB error: {e}"),
            Error::Corrupt(what) => write!(f, "corrupt peer table: {what}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

/// `address:port` as 6 bytes -- the form used both as this table's key
/// and on the wire in `discovery`'s `HOSTS` message.
pub fn encode_addr(addr: SocketAddrV4) -> [u8; ADDR_LEN] {
    let mut out = [0u8; ADDR_LEN];
    out[..4].copy_from_slice(&addr.ip().octets());
    out[4..].copy_from_slice(&addr.port().to_be_bytes());
    out
}

pub fn decode_addr(bytes: [u8; ADDR_LEN]) -> SocketAddrV4 {
    let ip = Ipv4Addr::new(bytes[0], bytes[1], bytes[2], bytes[3]);
    SocketAddrV4::new(ip, u16::from_be_bytes([bytes[4], bytes[5]]))
}

/// Whether `addr` could plausibly be a real peer at all: not the
/// unspecified address, broadcast, multicast, or port 0. Anything else
/// -- loopback and private ranges included, since test setups and LANs
/// legitimately use them -- is allowed.
pub fn is_plausible(addr: SocketAddrV4) -> bool {
    let ip = addr.ip();
    addr.port() != 0 && !ip.is_unspecified() && !ip.is_broadcast() && !ip.is_multicast()
}

/// What the table knows about one host.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostRecord {
    /// When this host last answered one of our requests, in Unix
    /// milliseconds -- `0` if it never has (still just a candidate).
    pub last_success_ms: u64,
    /// Consecutive unanswered requests since the last success.
    pub failures: u8,
}

impl HostRecord {
    pub fn is_verified(&self) -> bool {
        self.last_success_ms > 0
    }

    /// Answering now: it has answered, and no request since has gone
    /// unanswered. What counts as a peer (shared, counted).
    pub fn is_answering(&self) -> bool {
        self.is_verified() && self.failures == 0
    }

    fn to_bytes(self) -> [u8; RECORD_LEN] {
        let mut out = [0u8; RECORD_LEN];
        out[..8].copy_from_slice(&self.last_success_ms.to_be_bytes());
        out[8] = self.failures;
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != RECORD_LEN {
            return Err(Error::Corrupt("host record was not 9 bytes"));
        }
        Ok(HostRecord {
            last_success_ms: u64::from_be_bytes(bytes[..8].try_into().unwrap()),
            failures: bytes[8],
        })
    }
}

pub struct PeerTable {
    storage: Storage,
    hosts: Database<Bytes, Bytes>,
    max_hosts: usize,
    max_per_ip: usize,
    protected: HashSet<SocketAddrV4>,
}

impl PeerTable {
    /// Open (creating if absent) the peer table. `max_hosts` caps how
    /// many hosts it will ever hold, `max_per_ip` how many with one IP.
    pub fn open(storage: &Storage, max_hosts: usize, max_per_ip: usize) -> Result<Self> {
        let hosts = storage.database(PEERS_DB)?;
        Ok(PeerTable {
            storage: storage.clone(),
            hosts,
            max_hosts,
            max_per_ip,
            protected: HashSet::new(),
        })
    }

    /// Whether `addr`'s IP already has `max_per_ip` hosts (a seed always
    /// has room).
    fn ip_full(&self, wtxn: &heed::RwTxn, addr: SocketAddrV4) -> Result<bool> {
        if self.protected.contains(&addr) {
            return Ok(false);
        }
        let mut same = 0;
        for entry in self.hosts.iter(wtxn)? {
            let (key, _) = entry?;
            if key[..4] == addr.ip().octets() {
                same += 1;
            }
        }
        Ok(same >= self.max_per_ip)
    }

    /// Hosts never evicted to make room (the seeds).
    pub fn protect(&mut self, addrs: impl IntoIterator<Item = SocketAddrV4>) {
        self.protected.extend(addrs);
    }

    /// Room for one more host in a full table, made by evicting the host
    /// silent longest among those not answering now -- never answered
    /// first, then the oldest last success -- if there is one (not
    /// protected). Whether there's room.
    fn make_room(&self, wtxn: &mut heed::RwTxn) -> Result<bool> {
        if (self.hosts.len(wtxn)? as usize) < self.max_hosts {
            return Ok(true);
        }
        let mut victim: Option<([u8; ADDR_LEN], HostRecord)> = None;
        for entry in self.hosts.iter(wtxn)? {
            let (key, value) = entry?;
            let key: [u8; ADDR_LEN] = key.try_into().map_err(|_| Error::Corrupt("host key was not 6 bytes"))?;
            let record = HostRecord::from_bytes(value)?;
            if (record.is_verified() && record.failures == 0) || self.protected.contains(&decode_addr(key)) {
                continue; // answering, or a seed: kept
            }
            let older = match victim {
                None => true,
                Some((_, v)) => (record.last_success_ms, std::cmp::Reverse(record.failures))
                    < (v.last_success_ms, std::cmp::Reverse(v.failures)),
            };
            if older {
                victim = Some((key, record));
            }
        }
        match victim {
            Some((key, _)) => {
                self.hosts.delete(wtxn, &key)?;
                Ok(true)
            }
            None => Ok(false),
        }
    }

    pub fn get(&self, addr: SocketAddrV4) -> Result<Option<HostRecord>> {
        let rtxn = self.storage.read_txn()?;
        match self.hosts.get(&rtxn, &encode_addr(addr))? {
            Some(bytes) => Ok(Some(HostRecord::from_bytes(bytes)?)),
            None => Ok(None),
        }
    }

    pub fn len(&self) -> Result<usize> {
        let rtxn = self.storage.read_txn()?;
        Ok(self.hosts.len(&rtxn)? as usize)
    }

    /// Add `addr` as a candidate, unless it's already known, not
    /// `is_plausible`, or the table is full of hosts that are answering
    /// (see `make_room`). Returns whether it was added.
    pub fn add_candidate(&self, addr: SocketAddrV4) -> Result<bool> {
        if !is_plausible(addr) {
            return Ok(false);
        }
        let key = encode_addr(addr);
        let mut wtxn = self.storage.write_txn()?;
        if self.hosts.get(&wtxn, &key)?.is_some() || self.ip_full(&wtxn, addr)? || !self.make_room(&mut wtxn)? {
            return Ok(false);
        }
        let record = HostRecord {
            last_success_ms: 0,
            failures: 0,
        };
        self.hosts.put(&mut wtxn, &key, &record.to_bytes())?;
        wtxn.commit()?;
        Ok(true)
    }

    /// `addr` answered a request at `now_ms`: mark it verified and clear
    /// its failures. Adds it if it wasn't known (a seed removed while
    /// the request was in flight, say) -- capacity permitting.
    pub fn record_success(&self, addr: SocketAddrV4, now_ms: u64) -> Result<()> {
        let key = encode_addr(addr);
        let mut wtxn = self.storage.write_txn()?;
        let known = self.hosts.get(&wtxn, &key)?.is_some();
        if !known && (self.ip_full(&wtxn, addr)? || !self.make_room(&mut wtxn)?) {
            return Ok(());
        }
        let record = HostRecord {
            last_success_ms: now_ms.max(1),
            failures: 0,
        };
        self.hosts.put(&mut wtxn, &key, &record.to_bytes())?;
        wtxn.commit()?;
        Ok(())
    }

    /// A request to `addr` went unanswered at `now_ms`: one more failure.
    /// The host is kept and asked again -- unless it has never answered
    /// and this was its `NEVER_ANSWERED_TRIES`th, or it last answered
    /// `SILENT_DROP_MS` ago or more (and isn't a seed): then it's removed.
    /// Returns whether it was.
    pub fn record_failure(&self, addr: SocketAddrV4, now_ms: u64) -> Result<bool> {
        let key = encode_addr(addr);
        let mut wtxn = self.storage.write_txn()?;
        let Some(bytes) = self.hosts.get(&wtxn, &key)? else {
            return Ok(false);
        };
        let mut record = HostRecord::from_bytes(bytes)?;
        record.failures = record.failures.saturating_add(1);
        let gone = if record.is_verified() {
            now_ms.saturating_sub(record.last_success_ms) >= SILENT_DROP_MS
        } else {
            record.failures >= NEVER_ANSWERED_TRIES
        };
        let removed = gone && !self.protected.contains(&addr);
        if removed {
            self.hosts.delete(&mut wtxn, &key)?;
        } else {
            self.hosts.put(&mut wtxn, &key, &record.to_bytes())?;
        }
        wtxn.commit()?;
        Ok(removed)
    }

    /// Drop `addr` from the table outright, whatever its state.
    pub fn remove(&self, addr: SocketAddrV4) -> Result<()> {
        let mut wtxn = self.storage.write_txn()?;
        self.hosts.delete(&mut wtxn, &encode_addr(addr))?;
        wtxn.commit()?;
        Ok(())
    }

    /// Every host in the table, verified or not.
    pub fn all(&self) -> Result<Vec<(SocketAddrV4, HostRecord)>> {
        let rtxn = self.storage.read_txn()?;
        let mut out = Vec::new();
        for entry in self.hosts.iter(&rtxn)? {
            let (key, value) = entry?;
            let key: [u8; ADDR_LEN] = key.try_into().map_err(|_| Error::Corrupt("host key was not 6 bytes"))?;
            out.push((decode_addr(key), HostRecord::from_bytes(value)?));
        }
        Ok(out)
    }

    /// Up to `limit` hosts worth sharing with another peer: verified,
    /// with no failures since, most recently confirmed first, and never
    /// `exclude` (the peer asking, which has no use for its own address).
    pub fn active(&self, limit: usize, exclude: SocketAddrV4) -> Result<Vec<SocketAddrV4>> {
        let mut hosts: Vec<_> = self
            .all()?
            .into_iter()
            .filter(|(addr, record)| record.is_answering() && *addr != exclude)
            .collect();
        hosts.sort_by_key(|(_, record)| std::cmp::Reverse(record.last_success_ms));
        Ok(hosts.into_iter().take(limit).map(|(addr, _)| addr).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("peers-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn open(max_hosts: usize) -> (TempDir, Storage, PeerTable) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let table = PeerTable::open(&storage, max_hosts, 4).unwrap();
        (dir, storage, table)
    }

    fn addr(last_octet: u8, port: u16) -> SocketAddrV4 {
        SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, last_octet), port)
    }

    #[test]
    fn addresses_roundtrip_through_their_encoding() {
        let a = SocketAddrV4::new(Ipv4Addr::new(192, 168, 1, 200), 54321);
        assert_eq!(decode_addr(encode_addr(a)), a);
    }

    #[test]
    fn implausible_addresses_are_never_added() {
        let (_dir, _storage, table) = open(10);
        assert!(!table.add_candidate(SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 1)).unwrap());
        assert!(!table.add_candidate(SocketAddrV4::new(Ipv4Addr::BROADCAST, 1)).unwrap());
        assert!(!table.add_candidate(SocketAddrV4::new(Ipv4Addr::new(224, 0, 0, 1), 1)).unwrap());
        assert!(!table.add_candidate(addr(1, 0)).unwrap());
        assert_eq!(table.len().unwrap(), 0);
    }

    #[test]
    fn a_candidate_is_unverified_until_it_answers() {
        let (_dir, _storage, table) = open(10);
        assert!(table.add_candidate(addr(1, 9000)).unwrap());
        assert!(!table.get(addr(1, 9000)).unwrap().unwrap().is_verified());

        table.record_success(addr(1, 9000), 5_000).unwrap();
        let record = table.get(addr(1, 9000)).unwrap().unwrap();
        assert!(record.is_verified());
        assert_eq!(record.last_success_ms, 5_000);
    }

    #[test]
    fn adding_a_known_host_again_changes_nothing() {
        let (_dir, _storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_success(addr(1, 9000), 5_000).unwrap();

        assert!(!table.add_candidate(addr(1, 9000)).unwrap());
        assert!(table.get(addr(1, 9000)).unwrap().unwrap().is_verified());
    }

    #[test]
    fn a_host_that_answered_is_kept_for_a_week_of_silence() {
        let (_dir, _storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_success(addr(1, 9000), 5_000).unwrap();
        for _ in 0..100 {
            assert!(!table.record_failure(addr(1, 9000), 5_000 + SILENT_DROP_MS - 1).unwrap());
        }
        assert_eq!(table.get(addr(1, 9000)).unwrap().unwrap().failures, 100);
        assert!(table.record_failure(addr(1, 9000), 5_000 + SILENT_DROP_MS).unwrap());
        assert_eq!(table.get(addr(1, 9000)).unwrap(), None);
    }

    #[test]
    fn a_host_that_never_answered_is_dropped_after_a_few_tries() {
        let (_dir, _storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        for _ in 1..NEVER_ANSWERED_TRIES {
            assert!(!table.record_failure(addr(1, 9000), 0).unwrap());
        }
        assert!(table.record_failure(addr(1, 9000), 0).unwrap());
        assert_eq!(table.get(addr(1, 9000)).unwrap(), None);
    }

    #[test]
    fn seeds_are_never_dropped() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut table = PeerTable::open(&storage, 10, 4).unwrap();
        table.protect([addr(1, 9000), addr(2, 9000)]);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.add_candidate(addr(2, 9000)).unwrap();
        table.record_success(addr(2, 9000), 5_000).unwrap();
        for _ in 0..10 {
            table.record_failure(addr(1, 9000), 0).unwrap(); // never answered
            table.record_failure(addr(2, 9000), 5_000 + 10 * SILENT_DROP_MS).unwrap(); // long silent
        }
        assert!(table.get(addr(1, 9000)).unwrap().is_some());
        assert!(table.get(addr(2, 9000)).unwrap().is_some());
    }

    #[test]
    fn at_most_max_per_ip_hosts_share_an_ip() {
        let (_dir, _storage, table) = open(100);
        for port in 1..=4 {
            assert!(table.add_candidate(addr(1, port)).unwrap());
        }
        assert!(!table.add_candidate(addr(1, 5)).unwrap());
        assert!(table.add_candidate(addr(2, 5)).unwrap());
        table.record_success(addr(1, 6), 1_000).unwrap(); // nor by answering
        assert_eq!(table.get(addr(1, 6)).unwrap(), None);
    }

    #[test]
    fn a_success_resets_the_failure_count() {
        let (_dir, _storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_failure(addr(1, 9000), 0).unwrap();
        table.record_failure(addr(1, 9000), 0).unwrap();
        table.record_success(addr(1, 9000), 5_000).unwrap();
        assert_eq!(table.get(addr(1, 9000)).unwrap().unwrap().failures, 0);
        assert_eq!(table.active(10, addr(99, 1)).unwrap(), vec![addr(1, 9000)]);
    }

    #[test]
    fn a_full_table_of_answering_hosts_refuses_new_candidates() {
        let (_dir, _storage, table) = open(2);
        assert!(table.add_candidate(addr(1, 9000)).unwrap());
        assert!(table.add_candidate(addr(2, 9000)).unwrap());
        table.record_success(addr(1, 9000), 1_000).unwrap();
        table.record_success(addr(2, 9000), 2_000).unwrap();
        assert!(!table.add_candidate(addr(3, 9000)).unwrap());
        assert_eq!(table.len().unwrap(), 2);
    }

    #[test]
    fn a_full_table_evicts_the_host_silent_longest() {
        let (_dir, _storage, table) = open(3);
        for i in 1..=3 {
            table.add_candidate(addr(i, 9000)).unwrap();
        }
        table.record_success(addr(1, 9000), 3_000).unwrap(); // answering: kept
        table.record_success(addr(2, 9000), 1_000).unwrap();
        table.record_failure(addr(2, 9000), 0).unwrap(); // silent since 1,000
        table.record_success(addr(3, 9000), 2_000).unwrap();
        table.record_failure(addr(3, 9000), 0).unwrap(); // silent since 2,000

        assert!(table.add_candidate(addr(4, 9000)).unwrap());
        assert_eq!(table.get(addr(2, 9000)).unwrap(), None);
        assert!(table.get(addr(3, 9000)).unwrap().is_some());

        // A host that never answered goes before any that has.
        table.record_failure(addr(4, 9000), 0).unwrap();
        assert!(table.add_candidate(addr(5, 9000)).unwrap());
        assert_eq!(table.get(addr(4, 9000)).unwrap(), None);
        assert!(table.get(addr(3, 9000)).unwrap().is_some());
    }

    #[test]
    fn protected_hosts_are_never_evicted() {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut table = PeerTable::open(&storage, 1, 4).unwrap();
        table.protect([addr(1, 9000)]);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_failure(addr(1, 9000), 0).unwrap(); // a silent seed
        assert!(!table.add_candidate(addr(2, 9000)).unwrap());
        assert!(table.get(addr(1, 9000)).unwrap().is_some());
    }

    #[test]
    fn active_lists_only_verified_healthy_hosts_newest_first() {
        let (_dir, _storage, table) = open(10);
        for i in 1..=4 {
            table.add_candidate(addr(i, 9000)).unwrap();
        }
        table.record_success(addr(1, 9000), 1_000).unwrap();
        table.record_success(addr(2, 9000), 3_000).unwrap();
        table.record_success(addr(3, 9000), 2_000).unwrap();
        table.record_failure(addr(3, 9000), 0).unwrap(); // verified, but now failing
        // addr(4) never answered.

        let exclude = addr(99, 1);
        assert_eq!(table.active(10, exclude).unwrap(), vec![addr(2, 9000), addr(1, 9000)]);
        assert_eq!(table.active(1, exclude).unwrap(), vec![addr(2, 9000)]);
        assert_eq!(table.active(10, addr(2, 9000)).unwrap(), vec![addr(1, 9000)]);
    }

    #[test]
    fn remove_drops_a_host_whatever_its_state() {
        let (_dir, _storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_success(addr(1, 9000), 5_000).unwrap();
        table.remove(addr(1, 9000)).unwrap();
        assert_eq!(table.get(addr(1, 9000)).unwrap(), None);
    }

    #[test]
    fn the_table_persists_across_reopening() {
        let (_dir, storage, table) = open(10);
        table.add_candidate(addr(1, 9000)).unwrap();
        table.record_success(addr(1, 9000), 5_000).unwrap();
        drop(table);

        let reopened = PeerTable::open(&storage, 10, 4).unwrap();
        assert_eq!(reopened.get(addr(1, 9000)).unwrap().unwrap().last_success_ms, 5_000);
    }
}

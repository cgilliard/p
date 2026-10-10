//! Peer discovery over UDP: seeds plus peer exchange.
//!
//! A node starts from a configured list of seed hosts (IPv4 `addr:port`)
//! and sends each a `GET_HOSTS` request. A host answers with `HOSTS`: up
//! to some limit of the hosts *it* has verified as reachable. Every host
//! learned that way goes into the persistent `peers::PeerTable` as a
//! candidate, and is itself sent `GET_HOSTS` in turn -- which both
//! verifies it (an answer proves it's reachable) and learns its hosts.
//! Every known host is re-probed every `probe_interval_ms`, however long
//! it's been silent -- a host is only ever displaced by a new one, and
//! never a seed (see `peers`) -- so a node finds its peers again when they
//! come back (after a restart, say), not only when it restarts itself.
//! That's the whole protocol: two message types.
//!
//! # Bare-metal shape
//!
//! Everything here is datagrams in, datagrams out. `Discovery` itself
//! does no network I/O and never reads a clock: the caller hands it each
//! received message and the current time, and gets back the packets to
//! send. `net::Node` drives it over a datagram socket. The wire format
//! lives in `wire`.
//!
//! # Abuse resistance
//!
//! - **Spoofed replies:** a `HOSTS` is only accepted from the exact
//!   address a request is outstanding to, carrying that request's
//!   nonce. Nonces come from a keyed hash of a counter (`poseidon2`,
//!   keyed by a caller-supplied secret), so they can't be predicted from
//!   earlier ones. An off-path attacker can't inject addresses.
//! - **Reflection/amplification:** UDP source addresses are forgeable,
//!   so a reply could be aimed at a victim. A `HOSTS` reply is never
//!   more than `AMPLIFICATION_FACTOR` times the size of the request that
//!   prompted it (QUIC's rule); `GET_HOSTS` is padded by its sender to
//!   make room for as many hosts as it asks for.
//! - **Cookies:** requests whose replies are much bigger than they are
//!   (`GET_CHUNKS`, in `transfer`) can't follow that rule, so they must
//!   instead prove the requester really receives packets at its source
//!   address. Every `HOSTS` reply carries a `cookie` for the requester:
//!   a keyed hash of its address, under a secret only this node knows.
//!   Quoting it back proves the requester saw our reply -- an attacker
//!   forging a victim's address never does. Checking one is stateless
//!   (`check_cookie` just recomputes it), the same idea as DNS cookies
//!   or a QUIC retry token.
//! - **Unverified addresses are never repeated:** only hosts this node
//!   has itself heard back from are shared (`PeerTable::active`).
//!
//! # Talking to ourselves
//!
//! A node can't know every address it's reachable at (all its
//! interfaces, a NAT's public mapping), so its own address can reach its
//! table -- most simply when every node is handed the same seed list,
//! seed included. It gives itself away the moment it asks itself: a
//! `GET_HOSTS` arrives carrying a nonce from one of *our own*
//! outstanding requests. That address is then dropped from the table,
//! remembered as our own (`self_addrs`), and never added, shared, or
//! asked again -- the same trick Bitcoin's `version` nonce uses.

#![allow(dead_code)]

use crate::peers::{self, PeerTable};
use crate::wire::{self, MAX_HOSTS_PER_PACKET, Message};
use std::collections::{HashMap, HashSet};
use std::net::{SocketAddr, SocketAddrV4};

#[derive(Clone, Debug)]
pub struct Config {
    /// Hosts to ask first, every time the node starts.
    pub seeds: Vec<SocketAddrV4>,
    /// The most hosts this node puts in one `HOSTS` reply, and the most
    /// it asks for (and accepts) in one. Capped at `MAX_HOSTS_PER_PACKET`.
    pub share_limit: u16,
    /// How often each known host is re-asked, in milliseconds -- both
    /// to keep confirming it's reachable and to learn new hosts.
    pub probe_interval_ms: u64,
    /// How long a request may go unanswered before it counts as a
    /// failure, in milliseconds.
    pub response_timeout_ms: u64,
}

/// A datagram to send.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outgoing {
    pub to: SocketAddrV4,
    pub bytes: Vec<u8>,
}

struct Pending {
    nonce: u64,
    sent_at_ms: u64,
}

/// The discovery protocol's state, with no I/O of its own -- see the
/// module docs.
pub struct Discovery {
    config: Config,
    table: PeerTable,
    nonce_key: [u8; 32],
    nonce_counter: u64,
    /// xorshift64 state, for handing out hosts in a random order.
    shuffle_state: u64,
    /// The secret behind the cookies this node issues -- derived from
    /// `nonce_key`, under a different domain, so the two never coincide.
    cookie_key: [u8; 32],
    /// The cookie each peer issued *us*, from its latest `HOSTS` reply --
    /// what we quote back when asking it for chunks.
    peer_cookies: HashMap<SocketAddrV4, u64>,
    /// Requests awaiting a reply, by the host they were sent to -- at
    /// most one outstanding per host.
    pending: HashMap<SocketAddrV4, Pending>,
    /// When each host was last sent a request -- in memory only, so a
    /// restart re-probes everything right away, which is what a freshly
    /// started node wants anyway.
    last_probe_ms: HashMap<SocketAddrV4, u64>,
    /// Addresses found to be this node itself -- see the module docs.
    /// In memory only: a restart may rediscover them the same way.
    self_addrs: HashSet<SocketAddrV4>,
}

impl Discovery {
    /// `nonce_key` must be secret and unpredictable (fresh random bytes
    /// each run) -- it's what keeps request nonces unguessable.
    pub fn new(config: Config, mut table: PeerTable, nonce_key: [u8; 32]) -> Self {
        table.protect(config.seeds.iter().copied());
        Discovery {
            config,
            table,
            nonce_key,
            nonce_counter: 0,
            shuffle_state: u64::from_be_bytes(nonce_key[24..].try_into().unwrap()) | 1,
            cookie_key: crate::poseidon2::hash_bytes_32(&[&nonce_key[..], b"discovery cookie key"].concat()),
            peer_cookies: HashMap::new(),
            pending: HashMap::new(),
            last_probe_ms: HashMap::new(),
            self_addrs: HashSet::new(),
        }
    }

    /// Shuffle `items` (Fisher-Yates, xorshift64): spreading load, not
    /// secrecy.
    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let mut x = self.shuffle_state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.shuffle_state = x;
            items.swap(i, (x % (i as u64 + 1)) as usize);
        }
    }

    pub fn table(&self) -> &PeerTable {
        &self.table
    }

    /// Addresses this node has found to be itself.
    pub fn self_addrs(&self) -> &HashSet<SocketAddrV4> {
        &self.self_addrs
    }

    /// `add_candidate`, unless `addr` is this node itself.
    fn add_candidate(&self, addr: SocketAddrV4) -> peers::Result<()> {
        if !self.self_addrs.contains(&addr) {
            self.table.add_candidate(addr)?;
        }
        Ok(())
    }

    /// `addr` turned out to be this node: forget it as a peer, for good.
    fn mark_self(&mut self, addr: SocketAddrV4) -> peers::Result<()> {
        self.self_addrs.insert(addr);
        self.pending.remove(&addr);
        self.last_probe_ms.remove(&addr);
        self.peer_cookies.remove(&addr);
        self.table.remove(addr)
    }

    /// The cookie this node issues to `addr` -- see the module docs.
    fn issue_cookie(&self, addr: SocketAddrV4) -> u64 {
        let mut input = [0u8; 32 + peers::ADDR_LEN];
        input[..32].copy_from_slice(&self.cookie_key);
        input[32..].copy_from_slice(&peers::encode_addr(addr));
        let digest = crate::poseidon2::hash_bytes_32(&input);
        u64::from_be_bytes(digest[..8].try_into().unwrap())
    }

    /// Whether `cookie` is the one this node issued to `from`.
    pub fn check_cookie(&self, from: SocketAddrV4, cookie: u64) -> bool {
        self.issue_cookie(from) == cookie
    }

    /// The cookie `peer` issued us, if it has ever answered us.
    pub fn cookie_from(&self, peer: SocketAddrV4) -> Option<u64> {
        self.peer_cookies.get(&peer).copied()
    }

    fn share_limit(&self) -> usize {
        (self.config.share_limit as usize).min(MAX_HOSTS_PER_PACKET)
    }

    fn next_nonce(&mut self) -> u64 {
        let mut input = [0u8; 40];
        input[..32].copy_from_slice(&self.nonce_key);
        input[32..].copy_from_slice(&self.nonce_counter.to_be_bytes());
        self.nonce_counter += 1;
        let digest = crate::poseidon2::hash_bytes_32(&input);
        u64::from_be_bytes(digest[..8].try_into().unwrap())
    }

    fn request(&mut self, to: SocketAddrV4, now_ms: u64) -> Outgoing {
        let nonce = self.next_nonce();
        self.pending.insert(to, Pending { nonce, sent_at_ms: now_ms });
        self.last_probe_ms.insert(to, now_ms);
        let message = Message::GetHosts {
            nonce,
            max: self.share_limit() as u16,
        };
        Outgoing {
            to,
            bytes: message.encode(),
        }
    }

    /// Begin: record the seeds as candidates and ask each of them for
    /// hosts directly (even if the table is too full to hold them --
    /// what they answer with is still worth hearing), then anything
    /// else `tick` would send.
    pub fn start(&mut self, now_ms: u64) -> peers::Result<Vec<Outgoing>> {
        let mut out = Vec::new();
        for seed in self.config.seeds.clone() {
            if !peers::is_plausible(seed) || self.self_addrs.contains(&seed) {
                continue;
            }
            self.add_candidate(seed)?;
            out.push(self.request(seed, now_ms));
        }
        out.extend(self.tick(now_ms)?);
        Ok(out)
    }

    /// Housekeeping, to be called regularly: count every request that's
    /// timed out as a failure, then re-ask every known host that's due.
    pub fn tick(&mut self, now_ms: u64) -> peers::Result<Vec<Outgoing>> {
        let timeout = self.config.response_timeout_ms;
        let expired: Vec<SocketAddrV4> = self
            .pending
            .iter()
            .filter(|(_, p)| now_ms >= p.sent_at_ms + timeout)
            .map(|(addr, _)| *addr)
            .collect();
        for addr in expired {
            self.pending.remove(&addr);
            self.table.record_failure(addr)?; // kept: asked again next interval
        }

        let interval = self.config.probe_interval_ms;
        let mut out = Vec::new();
        for (addr, _) in self.table.all()? {
            let due = self.last_probe_ms.get(&addr).is_none_or(|&last| now_ms >= last + interval);
            if due && !self.pending.contains_key(&addr) {
                out.push(self.request(addr, now_ms));
            }
        }
        Ok(out)
    }

    /// Handle one received datagram from `from`. Anything that isn't a
    /// well-formed discovery message is ignored.
    pub fn handle(&mut self, from: SocketAddr, bytes: &[u8], now_ms: u64) -> peers::Result<Vec<Outgoing>> {
        let SocketAddr::V4(from) = from else {
            return Ok(Vec::new());
        };
        match Message::decode(bytes) {
            Some(message) => self.handle_message(from, &message, bytes.len(), now_ms),
            None => Ok(Vec::new()),
        }
    }

    /// `handle`, for an already-decoded message that arrived as a
    /// `packet_len`-byte datagram. Non-discovery messages are ignored.
    pub fn handle_message(
        &mut self,
        from: SocketAddrV4,
        message: &Message,
        packet_len: usize,
        now_ms: u64,
    ) -> peers::Result<Vec<Outgoing>> {
        match *message {
            Message::GetHosts { nonce, max } => {
                // One of our own requests, arriving back at us: whatever
                // address we sent it to is this node.
                let sent_to_self = self
                    .pending
                    .iter()
                    .find(|(_, p)| p.nonce == nonce)
                    .map(|(addr, _)| *addr);
                if let Some(addr) = sent_to_self {
                    self.mark_self(addr)?;
                    self.mark_self(from)?;
                    return Ok(Vec::new());
                }
                // Unverified -- a source address proves nothing over
                // UDP -- but worth probing: it's evidently a node.
                self.add_candidate(from)?;
                let limit = (max as usize)
                    .min(self.share_limit())
                    .min(wire::hosts_amplification_limit(packet_len));
                // A random sample of the answering hosts, so different
                // askers are introduced to different parts of the network.
                let mut hosts = self.table.active(usize::MAX, from)?;
                self.shuffle(&mut hosts);
                hosts.truncate(limit);
                let reply = Message::Hosts {
                    nonce,
                    cookie: self.issue_cookie(from),
                    hosts,
                };
                Ok(vec![Outgoing {
                    to: from,
                    bytes: reply.encode(),
                }])
            }
            Message::Hosts { nonce, cookie, ref hosts } => {
                match self.pending.get(&from) {
                    Some(p) if p.nonce == nonce => {}
                    _ => return Ok(Vec::new()),
                }
                self.pending.remove(&from);
                self.peer_cookies.insert(from, cookie);
                self.table.record_success(from, now_ms)?;
                for &host in hosts.iter().take(self.share_limit()) {
                    self.add_candidate(host)?;
                }
                Ok(Vec::new())
            }
            _ => Ok(Vec::new()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::Storage;
    use std::net::Ipv4Addr;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("discovery-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn addr(last_octet: u8, port: u16) -> SocketAddrV4 {
        SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, last_octet), port)
    }

    fn config(seeds: Vec<SocketAddrV4>) -> Config {
        Config {
            seeds,
            share_limit: 10,
            probe_interval_ms: 1_000,
            response_timeout_ms: 100,
        }
    }

    fn discovery(config: Config) -> (TempDir, Discovery) {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let table = PeerTable::open(&storage, 100).unwrap();
        (dir, Discovery::new(config, table, [7u8; 32]))
    }

    /// The single `GET_HOSTS` nonce sent to `to` in `out`.
    fn nonce_sent_to(out: &[Outgoing], to: SocketAddrV4) -> u64 {
        let packet = out.iter().find(|p| p.to == to).expect("no packet sent there");
        match Message::decode(&packet.bytes) {
            Some(Message::GetHosts { nonce, .. }) => nonce,
            other => panic!("expected GET_HOSTS, got {other:?}"),
        }
    }

    fn hosts_reply(nonce: u64, hosts: Vec<SocketAddrV4>) -> Vec<u8> {
        Message::Hosts { nonce, cookie: 0, hosts }.encode()
    }

    #[test]
    fn start_asks_every_seed_for_hosts() {
        let seeds = vec![addr(1, 9000), addr(2, 9000)];
        let (_dir, mut d) = discovery(config(seeds.clone()));
        let out = d.start(0).unwrap();

        assert_eq!(out.len(), 2);
        for seed in seeds {
            nonce_sent_to(&out, seed);
            assert!(d.table().get(seed).unwrap().is_some());
        }
    }

    #[test]
    fn a_matching_reply_verifies_the_sender_and_adds_its_hosts() {
        let seed = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![seed]));
        let out = d.start(0).unwrap();
        let nonce = nonce_sent_to(&out, seed);

        let reply = hosts_reply(nonce, vec![addr(2, 9000), addr(3, 9000)]);
        d.handle(SocketAddr::V4(seed), &reply, 50).unwrap();

        assert_eq!(d.table().get(seed).unwrap().unwrap().last_success_ms, 50);
        assert!(!d.table().get(addr(2, 9000)).unwrap().unwrap().is_verified());
        assert!(d.table().get(addr(3, 9000)).unwrap().is_some());
    }

    #[test]
    fn unsolicited_or_mismatched_replies_are_ignored() {
        let seed = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![seed]));
        let out = d.start(0).unwrap();
        let nonce = nonce_sent_to(&out, seed);

        // Wrong nonce, from the right host.
        d.handle(SocketAddr::V4(seed), &hosts_reply(nonce ^ 1, vec![addr(2, 9000)]), 10)
            .unwrap();
        // Right nonce, from a host never asked.
        d.handle(SocketAddr::V4(addr(5, 9000)), &hosts_reply(nonce, vec![addr(3, 9000)]), 10)
            .unwrap();

        assert!(!d.table().get(seed).unwrap().unwrap().is_verified());
        assert_eq!(d.table().get(addr(2, 9000)).unwrap(), None);
        assert_eq!(d.table().get(addr(3, 9000)).unwrap(), None);
        assert_eq!(d.table().get(addr(5, 9000)).unwrap(), None);
    }

    #[test]
    fn a_reply_is_only_accepted_once() {
        let seed = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![seed]));
        let out = d.start(0).unwrap();
        let nonce = nonce_sent_to(&out, seed);

        d.handle(SocketAddr::V4(seed), &hosts_reply(nonce, vec![]), 10).unwrap();
        d.handle(SocketAddr::V4(seed), &hosts_reply(nonce, vec![addr(2, 9000)]), 20)
            .unwrap();
        assert_eq!(d.table().get(addr(2, 9000)).unwrap(), None);
    }

    #[test]
    fn a_host_that_stops_answering_is_kept_and_asked_again() {
        let seed = addr(1, 9000);
        let learned = addr(2, 9000);
        let mut cfg = config(vec![seed]);
        cfg.probe_interval_ms = 0; // re-ask as soon as the last one times out
        let (_dir, mut d) = discovery(cfg);

        let mut now = 0;
        let out = d.start(now).unwrap();
        let nonce = nonce_sent_to(&out, seed);
        d.handle(SocketAddr::V4(seed), &hosts_reply(nonce, vec![learned]), 10).unwrap();
        for _ in 0..10 {
            now += 100;
            d.tick(now).unwrap();
        }
        assert!(d.table().get(learned).unwrap().is_some());
        now += 100;
        nonce_sent_to(&d.tick(now).unwrap(), learned);
    }

    #[test]
    fn a_seed_that_never_answers_is_kept_and_asked_again() {
        let seed = addr(1, 9000);
        let mut cfg = config(vec![seed]);
        cfg.probe_interval_ms = 0;
        let (_dir, mut d) = discovery(cfg);

        let mut now = 0;
        d.start(now).unwrap();
        for _ in 0..10 {
            now += 100;
            d.tick(now).unwrap();
        }
        assert!(d.table().get(seed).unwrap().is_some());
        now += 100;
        let out = d.tick(now).unwrap();
        nonce_sent_to(&out, seed); // still asked
    }

    #[test]
    fn a_verified_host_is_not_re_asked_before_the_probe_interval() {
        let seed = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![seed]));
        let out = d.start(0).unwrap();
        let nonce = nonce_sent_to(&out, seed);
        d.handle(SocketAddr::V4(seed), &hosts_reply(nonce, vec![]), 10).unwrap();

        assert!(d.tick(500).unwrap().is_empty());
        let out = d.tick(1_000).unwrap();
        nonce_sent_to(&out, seed);
    }

    #[test]
    fn a_request_gets_only_active_hosts_and_never_its_own_address() {
        let (_dir, mut d) = discovery(config(vec![]));
        let requester = addr(9, 9000);
        for i in 1..=3 {
            d.table().add_candidate(addr(i, 9000)).unwrap();
        }
        d.table().record_success(addr(1, 9000), 100).unwrap();
        d.table().record_success(addr(2, 9000), 200).unwrap();
        d.table().record_success(requester, 300).unwrap();
        // addr(3) never verified.

        let request = Message::GetHosts { nonce: 5, max: 10 }.encode();
        let out = d.handle(SocketAddr::V4(requester), &request, 1_000).unwrap();

        assert_eq!(out.len(), 1);
        assert_eq!(out[0].to, requester);
        match Message::decode(&out[0].bytes) {
            Some(Message::Hosts { nonce, cookie, mut hosts }) => {
                assert_eq!((nonce, cookie), (5, d.issue_cookie(requester)));
                hosts.sort();
                assert_eq!(hosts, vec![addr(1, 9000), addr(2, 9000)]); // in a random order
            }
            other => panic!("expected HOSTS, got {other:?}"),
        }
    }

    #[test]
    fn replies_sample_the_answering_hosts_at_random() {
        let (_dir, mut d) = discovery(config(vec![]));
        for i in 1..=20 {
            d.table().add_candidate(addr(i, 9000)).unwrap();
            d.table().record_success(addr(i, 9000), i as u64).unwrap();
        }
        let mut seen = std::collections::HashSet::new();
        for n in 0..10 {
            let request = Message::GetHosts { nonce: n, max: 3 }.encode();
            let out = d.handle(SocketAddr::V4(addr(99, 9000)), &request, 1_000).unwrap();
            if let Some(Message::Hosts { hosts, .. }) = Message::decode(&out[0].bytes) {
                seen.extend(hosts);
            }
        }
        assert!(seen.len() > 3, "always the same three hosts: {seen:?}");
    }

    #[test]
    fn a_reply_honors_the_requested_max_and_the_share_limit() {
        let (_dir, mut d) = discovery(config(vec![]));
        for i in 1..=20 {
            d.table().add_candidate(addr(i, 9000)).unwrap();
            d.table().record_success(addr(i, 9000), i as u64).unwrap();
        }
        let requester = SocketAddr::V4(addr(99, 9000));

        let count = |out: Vec<Outgoing>| match Message::decode(&out[0].bytes) {
            Some(Message::Hosts { hosts, .. }) => hosts.len(),
            other => panic!("expected HOSTS, got {other:?}"),
        };

        let small = Message::GetHosts { nonce: 1, max: 3 }.encode();
        assert_eq!(count(d.handle(requester, &small, 0).unwrap()), 3);
        // Asks for more than share_limit (10) allows.
        let large = Message::GetHosts { nonce: 2, max: 100 }.encode();
        assert_eq!(count(d.handle(requester, &large, 0).unwrap()), 10);
    }

    /// A request that asks for a lot without paying for it in padding
    /// gets only what the amplification bound allows.
    #[test]
    fn an_unpadded_request_gets_a_reply_within_the_amplification_bound() {
        let (_dir, mut d) = discovery(config(vec![]));
        for i in 1..=20 {
            d.table().add_candidate(addr(i, 9000)).unwrap();
            d.table().record_success(addr(i, 9000), i as u64).unwrap();
        }

        let mut request = Message::GetHosts { nonce: 1, max: 10 }.encode();
        request.truncate(wire::HEADER_LEN + 8 + 2);
        let out = d.handle(SocketAddr::V4(addr(99, 9000)), &request, 0).unwrap();

        assert!(out[0].bytes.len() <= request.len() * wire::AMPLIFICATION_FACTOR);
        assert_eq!(
            Message::decode(&out[0].bytes).map(|m| matches!(m, Message::Hosts { .. })),
            Some(true)
        );
    }

    #[test]
    fn a_requester_becomes_a_candidate() {
        let (_dir, mut d) = discovery(config(vec![]));
        let requester = addr(9, 9000);
        let request = Message::GetHosts { nonce: 1, max: 10 }.encode();
        d.handle(SocketAddr::V4(requester), &request, 0).unwrap();

        let record = d.table().get(requester).unwrap().unwrap();
        assert!(!record.is_verified());
    }

    #[test]
    fn nonces_differ_from_request_to_request() {
        let (_dir, mut d) = discovery(config(vec![]));
        let a = d.next_nonce();
        let b = d.next_nonce();
        assert_ne!(a, b);
    }

    /// The classic way this happens: a node handed its own address as a
    /// seed. Its request comes straight back to it.
    #[test]
    fn a_node_that_asks_itself_recognizes_it_and_forgets_that_address() {
        let me = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![me]));
        let out = d.start(0).unwrap();
        let request = &out.iter().find(|p| p.to == me).unwrap().bytes;

        // The request arrives at ourselves.
        let reply = d.handle(SocketAddr::V4(me), request, 1).unwrap();

        assert!(reply.is_empty(), "must not answer itself");
        assert_eq!(d.table().get(me).unwrap(), None);
        assert!(d.self_addrs().contains(&me));

        // Never re-added from someone else's list, and never probed.
        let other = addr(2, 9000);
        d.table().add_candidate(other).unwrap();
        let out = d.tick(10_000).unwrap();
        let nonce = nonce_sent_to(&out, other);
        assert!(out.iter().all(|p| p.to != me));
        d.handle(SocketAddr::V4(other), &hosts_reply(nonce, vec![me]), 10_001)
            .unwrap();
        assert_eq!(d.table().get(me).unwrap(), None);
    }

    /// Our own address can also be learned under a name we can't
    /// predict (another interface, a NAT mapping) -- detection works on
    /// whatever address the request was sent to, not just seeds.
    #[test]
    fn a_self_address_learned_from_a_peer_is_caught_on_first_probe() {
        let (_dir, mut d) = discovery(config(vec![]));
        let alias = addr(5, 9000);
        d.table().add_candidate(alias).unwrap();

        let out = d.tick(0).unwrap();
        let request = &out.iter().find(|p| p.to == alias).unwrap().bytes;
        // It arrives from our "real" address, which differs from the alias.
        let real = addr(1, 9000);
        assert!(d.handle(SocketAddr::V4(real), request, 1).unwrap().is_empty());

        assert_eq!(d.table().get(alias).unwrap(), None);
        assert!(d.self_addrs().contains(&alias));
        assert!(d.self_addrs().contains(&real));
    }

    /// A peer's `HOSTS` reply carries the cookie it issued us, and we
    /// keep it for quoting back later.
    #[test]
    fn a_reply_records_the_cookie_the_peer_issued_us() {
        let seed = addr(1, 9000);
        let (_dir, mut d) = discovery(config(vec![seed]));
        let out = d.start(0).unwrap();
        let nonce = nonce_sent_to(&out, seed);
        assert_eq!(d.cookie_from(seed), None);

        let reply = Message::Hosts {
            nonce,
            cookie: 0xabcd,
            hosts: vec![],
        };
        d.handle(SocketAddr::V4(seed), &reply.encode(), 1).unwrap();
        assert_eq!(d.cookie_from(seed), Some(0xabcd));
    }

    /// The cookie we issue a requester checks out for that address, and
    /// only that address -- and two nodes' cookies differ.
    #[test]
    fn cookies_we_issue_check_out_only_for_their_own_address() {
        let (_dir, mut d) = discovery(config(vec![]));
        let requester = addr(9, 9000);
        let request = Message::GetHosts { nonce: 1, max: 10 }.encode();
        let out = d.handle(SocketAddr::V4(requester), &request, 0).unwrap();
        let Some(Message::Hosts { cookie, .. }) = Message::decode(&out[0].bytes) else {
            panic!("expected HOSTS");
        };

        assert!(d.check_cookie(requester, cookie));
        assert!(!d.check_cookie(addr(9, 9001), cookie));
        assert!(!d.check_cookie(requester, cookie ^ 1));

        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let other = Discovery::new(config(vec![]), PeerTable::open(&storage, 100).unwrap(), [8u8; 32]);
        assert!(!other.check_cookie(requester, cookie));
    }
}

//! Peer discovery over UDP: seeds plus peer exchange.
//!
//! A node starts from a configured list of seed hosts (IPv4 `addr:port`)
//! and sends each a `GET_HOSTS` request. A host answers with `HOSTS`: up
//! to some limit of the hosts *it* has verified as reachable. Every host
//! learned that way goes into the persistent `peers::PeerTable` as a
//! candidate, and is itself sent `GET_HOSTS` in turn -- which both
//! verifies it (an answer proves it's reachable) and learns its hosts.
//! Every known host is re-probed every `probe_interval_ms`; one that
//! stops answering accumulates failures and is eventually removed (see
//! `peers`). That's the whole protocol: two message types.
//!
//! # Bare-metal shape
//!
//! Everything here is datagrams in, datagrams out. `Discovery` itself
//! does no I/O at all and never reads a clock: the caller hands it each
//! received packet and the current time, and gets back the packets to
//! send. The only I/O-touching part is `Node`, which drives a
//! `Discovery` over anything implementing `Transport` (send/receive one
//! datagram) -- `std::net::UdpSocket` implements it here; a bare-metal
//! UDP stack can implement it the same way without touching the
//! protocol. Every packet is at most `MAX_PACKET` bytes, so no IP
//! fragmentation is ever needed (minimal stacks often can't reassemble).
//!
//! # Wire format
//!
//! Every packet: `MAGIC` (4) ‖ `VERSION` (1) ‖ type (1) ‖ body.
//!
//! - `GET_HOSTS` (type 1): `nonce` (u64) ‖ `max` (u16) ‖ zero padding.
//! - `HOSTS` (type 2): `nonce` (u64) ‖ `count` (u16) ‖ `count` × 6-byte
//!   addresses (`peers::encode_addr`).
//!
//! Integers are big-endian. A packet that doesn't parse exactly is
//! silently dropped -- there's no error reply, which an attacker could
//! only use as a reflector.
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

use crate::peers::{self, ADDR_LEN, PeerTable};
use std::collections::{HashMap, HashSet};
use std::net::{SocketAddr, SocketAddrV4};

pub const MAGIC: [u8; 4] = *b"TBRN";
pub const VERSION: u8 = 1;

/// Largest packet this protocol ever sends or accepts -- comfortably
/// under the 1280-byte IPv6 minimum MTU (and every realistic IPv4 path
/// MTU), so nothing is ever fragmented.
pub const MAX_PACKET: usize = 1200;

/// A reply is never more than this many times the size of its request.
pub const AMPLIFICATION_FACTOR: usize = 3;

const TYPE_GET_HOSTS: u8 = 1;
const TYPE_HOSTS: u8 = 2;

const HEADER_LEN: usize = MAGIC.len() + 2;
/// `nonce` + `max`/`count` -- the same shape for both message bodies.
const BODY_PREFIX_LEN: usize = 8 + 2;
const MIN_PACKET: usize = HEADER_LEN + BODY_PREFIX_LEN;

/// The most addresses a single `HOSTS` packet can carry within
/// `MAX_PACKET`.
pub const MAX_HOSTS_PER_PACKET: usize = (MAX_PACKET - MIN_PACKET) / ADDR_LEN;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
    GetHosts { nonce: u64, max: u16 },
    Hosts { nonce: u64, hosts: Vec<SocketAddrV4> },
}

/// Size of a `HOSTS` packet carrying `count` addresses.
fn hosts_packet_len(count: usize) -> usize {
    MIN_PACKET + count * ADDR_LEN
}

/// How many addresses a reply to a `request_len`-byte request may carry
/// without breaking the amplification bound.
fn amplification_limit(request_len: usize) -> usize {
    (request_len * AMPLIFICATION_FACTOR).saturating_sub(MIN_PACKET) / ADDR_LEN
}

impl Message {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MAX_PACKET);
        out.extend_from_slice(&MAGIC);
        out.push(VERSION);
        match self {
            Message::GetHosts { nonce, max } => {
                out.push(TYPE_GET_HOSTS);
                out.extend_from_slice(&nonce.to_be_bytes());
                out.extend_from_slice(&max.to_be_bytes());
                // Pad so the answer we're asking for fits under the
                // amplification bound: request_len * FACTOR >= reply_len.
                let max = (*max as usize).min(MAX_HOSTS_PER_PACKET);
                let needed = hosts_packet_len(max).div_ceil(AMPLIFICATION_FACTOR);
                if out.len() < needed {
                    out.resize(needed, 0);
                }
            }
            Message::Hosts { nonce, hosts } => {
                out.push(TYPE_HOSTS);
                out.extend_from_slice(&nonce.to_be_bytes());
                let hosts = &hosts[..hosts.len().min(MAX_HOSTS_PER_PACKET)];
                out.extend_from_slice(&(hosts.len() as u16).to_be_bytes());
                for host in hosts {
                    out.extend_from_slice(&peers::encode_addr(*host));
                }
            }
        }
        out
    }

    /// Parse a packet, or `None` if it isn't exactly a valid one.
    pub fn decode(bytes: &[u8]) -> Option<Message> {
        if bytes.len() < MIN_PACKET || bytes.len() > MAX_PACKET {
            return None;
        }
        if bytes[..4] != MAGIC || bytes[4] != VERSION {
            return None;
        }
        let nonce = u64::from_be_bytes(bytes[HEADER_LEN..HEADER_LEN + 8].try_into().unwrap());
        let n = u16::from_be_bytes(bytes[HEADER_LEN + 8..MIN_PACKET].try_into().unwrap());
        let rest = &bytes[MIN_PACKET..];
        match bytes[5] {
            // Padding is allowed (and required, for large `max`), but
            // must be zeros -- no room to smuggle anything else in.
            TYPE_GET_HOSTS if rest.iter().all(|&b| b == 0) => Some(Message::GetHosts { nonce, max: n }),
            TYPE_HOSTS if rest.len() == n as usize * ADDR_LEN => {
                let hosts = rest
                    .chunks_exact(ADDR_LEN)
                    .map(|chunk| peers::decode_addr(chunk.try_into().unwrap()))
                    .collect();
                Some(Message::Hosts { nonce, hosts })
            }
            _ => None,
        }
    }
}

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
    pub fn new(config: Config, table: PeerTable, nonce_key: [u8; 32]) -> Self {
        Discovery {
            config,
            table,
            nonce_key,
            nonce_counter: 0,
            pending: HashMap::new(),
            last_probe_ms: HashMap::new(),
            self_addrs: HashSet::new(),
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
        self.table.remove(addr)
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
            if self.table.record_failure(addr)? {
                self.last_probe_ms.remove(&addr);
            }
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
    /// well-formed, expected message is ignored.
    pub fn handle(&mut self, from: SocketAddr, bytes: &[u8], now_ms: u64) -> peers::Result<Vec<Outgoing>> {
        let SocketAddr::V4(from) = from else {
            return Ok(Vec::new());
        };
        match Message::decode(bytes) {
            Some(Message::GetHosts { nonce, max }) => {
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
                    .min(amplification_limit(bytes.len()));
                let hosts = self.table.active(limit, from)?;
                let reply = Message::Hosts { nonce, hosts };
                Ok(vec![Outgoing {
                    to: from,
                    bytes: reply.encode(),
                }])
            }
            Some(Message::Hosts { nonce, hosts }) => {
                match self.pending.get(&from) {
                    Some(p) if p.nonce == nonce => {}
                    _ => return Ok(Vec::new()),
                }
                self.pending.remove(&from);
                self.table.record_success(from, now_ms)?;
                for host in hosts.into_iter().take(self.share_limit()) {
                    self.add_candidate(host)?;
                }
                Ok(Vec::new())
            }
            None => Ok(Vec::new()),
        }
    }
}

/// One datagram socket, as `Node` needs it -- the seam between the
/// protocol and whatever UDP stack is underneath.
pub trait Transport {
    type Error: std::fmt::Debug;

    fn send_to(&mut self, bytes: &[u8], to: SocketAddrV4) -> Result<(), Self::Error>;

    /// Receive one datagram into `buf`, returning its length and
    /// sender, or `None` if nothing arrived within the transport's own
    /// wait (a timeout, or nothing ready on a non-blocking socket).
    fn recv_from(&mut self, buf: &mut [u8]) -> Result<Option<(usize, SocketAddr)>, Self::Error>;
}

/// `std`'s UDP socket. Set a read timeout (or non-blocking mode) on it
/// first, or `recv_from` blocks until a packet arrives and `Node::poll`
/// never gets to run `tick`.
impl Transport for std::net::UdpSocket {
    type Error = std::io::Error;

    fn send_to(&mut self, bytes: &[u8], to: SocketAddrV4) -> std::io::Result<()> {
        std::net::UdpSocket::send_to(self, bytes, to).map(|_| ())
    }

    fn recv_from(&mut self, buf: &mut [u8]) -> std::io::Result<Option<(usize, SocketAddr)>> {
        match std::net::UdpSocket::recv_from(self, buf) {
            Ok((len, from)) => Ok(Some((len, from))),
            Err(e) if matches!(e.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut) => Ok(None),
            Err(e) => Err(e),
        }
    }
}

#[derive(Debug)]
pub enum NodeError<E> {
    Peers(peers::Error),
    Transport(E),
}

impl<E> From<peers::Error> for NodeError<E> {
    fn from(e: peers::Error) -> Self {
        NodeError::Peers(e)
    }
}

/// A one-line, human-readable summary of a datagram, for `Node`'s log.
fn describe(bytes: &[u8]) -> String {
    match Message::decode(bytes) {
        Some(Message::GetHosts { nonce, max }) => format!("GET_HOSTS(nonce={nonce:016x}, max={max})"),
        Some(Message::Hosts { nonce, hosts }) => {
            let hosts: Vec<String> = hosts.iter().map(|h| h.to_string()).collect();
            format!("HOSTS(nonce={nonce:016x}, [{}])", hosts.join(", "))
        }
        None => format!("unparseable packet ({} bytes)", bytes.len()),
    }
}

/// A `Discovery` wired to a `Transport`.
pub struct Node<T: Transport> {
    pub discovery: Discovery,
    /// When set, print every datagram sent and received to stderr,
    /// prefixed with this label (the node's own port, say) -- a
    /// debugging aid, off by default.
    pub log: Option<String>,
    transport: T,
    tick_interval_ms: u64,
    next_tick_ms: Option<u64>,
    buf: Vec<u8>,
}

impl<T: Transport> Node<T> {
    /// `tick_interval_ms` is how often `Discovery::tick` runs -- it
    /// bounds how late a timeout or a due probe can be noticed, so keep
    /// it well under `response_timeout_ms`.
    pub fn new(discovery: Discovery, transport: T, tick_interval_ms: u64) -> Self {
        Node {
            discovery,
            log: None,
            transport,
            tick_interval_ms,
            next_tick_ms: None,
            buf: vec![0u8; MAX_PACKET + 1],
        }
    }

    fn send_all(&mut self, out: Vec<Outgoing>) {
        // A failed send is just a lost datagram, which this protocol
        // already tolerates (the request times out and is retried).
        for packet in out {
            let result = self.transport.send_to(&packet.bytes, packet.to);
            if let Some(label) = &self.log {
                match &result {
                    Ok(()) => eprintln!("[{label}] sent {} to {}", describe(&packet.bytes), packet.to),
                    Err(e) => eprintln!("[{label}] FAILED to send {} to {}: {e:?}", describe(&packet.bytes), packet.to),
                }
            }
        }
    }

    /// One step: on the first call, `Discovery::start`; afterwards,
    /// handle at most one received datagram, then `tick` if it's due.
    /// `now_ms` is read once per call by the caller.
    pub fn poll(&mut self, now_ms: u64) -> Result<(), NodeError<T::Error>> {
        let Some(next_tick) = self.next_tick_ms else {
            let out = self.discovery.start(now_ms)?;
            self.send_all(out);
            self.next_tick_ms = Some(now_ms + self.tick_interval_ms);
            return Ok(());
        };

        // One spare byte past MAX_PACKET, so an oversized datagram
        // shows up as too long (and is rejected) instead of being
        // silently truncated into something that parses.
        if let Some((len, from)) = self.transport.recv_from(&mut self.buf).map_err(NodeError::Transport)? {
            let packet = self.buf[..len].to_vec();
            if let Some(label) = &self.log {
                eprintln!("[{label}] recv {} from {from}", describe(&packet));
            }
            let out = self.discovery.handle(from, &packet, now_ms)?;
            self.send_all(out);
        }

        if now_ms >= next_tick {
            let out = self.discovery.tick(now_ms)?;
            self.send_all(out);
            self.next_tick_ms = Some(now_ms + self.tick_interval_ms);
        }
        Ok(())
    }

    /// `poll` forever, reading the time from `clock`, until `stop` is set.
    pub fn run(
        &mut self,
        clock: impl Fn() -> u64,
        stop: &std::sync::atomic::AtomicBool,
    ) -> Result<(), NodeError<T::Error>> {
        while !stop.load(std::sync::atomic::Ordering::Relaxed) {
            self.poll(clock())?;
        }
        Ok(())
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
        let table = PeerTable::open(&storage, 100, 3).unwrap();
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
        Message::Hosts { nonce, hosts }.encode()
    }

    #[test]
    fn messages_roundtrip() {
        let get = Message::GetHosts { nonce: 42, max: 17 };
        assert_eq!(Message::decode(&get.encode()), Some(get));
        let hosts = Message::Hosts {
            nonce: 43,
            hosts: vec![addr(1, 1), addr(2, 2)],
        };
        assert_eq!(Message::decode(&hosts.encode()), Some(hosts));
    }

    #[test]
    fn malformed_packets_are_rejected() {
        let good = Message::Hosts {
            nonce: 1,
            hosts: vec![addr(1, 1)],
        }
        .encode();

        let mut bad_magic = good.clone();
        bad_magic[0] ^= 1;
        let mut bad_version = good.clone();
        bad_version[4] = VERSION + 1;
        let mut bad_type = good.clone();
        bad_type[5] = 99;
        let truncated = &good[..good.len() - 1];
        let mut trailing = good.clone();
        trailing.push(0);
        let mut nonzero_padding = Message::GetHosts { nonce: 1, max: 50 }.encode();
        *nonzero_padding.last_mut().unwrap() = 1;

        for packet in [&bad_magic[..], &bad_version, &bad_type, truncated, &trailing, &nonzero_padding, &good[..3]] {
            assert_eq!(Message::decode(packet), None);
        }
        assert_eq!(Message::decode(&vec![0u8; MAX_PACKET + 1]), None);
    }

    #[test]
    fn every_packet_fits_the_size_limit() {
        let biggest = Message::Hosts {
            nonce: 0,
            hosts: vec![addr(1, 1); MAX_HOSTS_PER_PACKET + 50],
        }
        .encode();
        assert!(biggest.len() <= MAX_PACKET);
        let biggest_request = Message::GetHosts { nonce: 0, max: u16::MAX }.encode();
        assert!(biggest_request.len() <= MAX_PACKET);
    }

    /// A request is padded enough that a full answer to it stays within
    /// the amplification bound.
    #[test]
    fn a_request_is_padded_to_cover_the_reply_it_asks_for() {
        for max in [0u16, 1, 10, 100, MAX_HOSTS_PER_PACKET as u16] {
            let request = Message::GetHosts { nonce: 0, max }.encode();
            let reply_len = hosts_packet_len(max as usize);
            assert!(request.len() * AMPLIFICATION_FACTOR >= reply_len, "max = {max}");
            assert!(amplification_limit(request.len()) >= max as usize);
        }
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
    fn a_host_that_never_answers_is_removed_after_enough_timeouts() {
        let seed = addr(1, 9000);
        let mut cfg = config(vec![seed]);
        cfg.probe_interval_ms = 0; // re-ask as soon as the last one times out
        let (_dir, mut d) = discovery(cfg);

        let mut now = 0;
        d.start(now).unwrap();
        for _ in 0..3 {
            now += 100;
            d.tick(now).unwrap();
        }
        assert_eq!(d.table().get(seed).unwrap(), None);
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
        assert_eq!(
            Message::decode(&out[0].bytes),
            Some(Message::Hosts {
                nonce: 5,
                hosts: vec![addr(2, 9000), addr(1, 9000)]
            })
        );
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
        request.truncate(MIN_PACKET);
        let out = d.handle(SocketAddr::V4(addr(99, 9000)), &request, 0).unwrap();

        assert!(out[0].bytes.len() <= request.len() * AMPLIFICATION_FACTOR);
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

    /// Three real nodes on loopback UDP: B only knows A, A only knows C.
    /// B should end up having verified C itself, purely through A.
    #[test]
    fn hosts_propagate_between_real_udp_nodes() {
        use std::net::UdpSocket;
        use std::time::Duration;

        fn bind() -> (UdpSocket, SocketAddrV4) {
            let socket = UdpSocket::bind("127.0.0.1:0").unwrap();
            socket.set_read_timeout(Some(Duration::from_millis(5))).unwrap();
            let SocketAddr::V4(local) = socket.local_addr().unwrap() else {
                unreachable!()
            };
            (socket, local)
        }

        fn node(seeds: Vec<SocketAddrV4>, socket: UdpSocket, key: u8) -> (TempDir, Node<UdpSocket>) {
            let dir = TempDir::new();
            let storage = Storage::open(&dir.0).unwrap();
            let table = PeerTable::open(&storage, 100, 3).unwrap();
            let cfg = Config {
                seeds,
                share_limit: 10,
                probe_interval_ms: 50,
                response_timeout_ms: 500,
            };
            (dir, Node::new(Discovery::new(cfg, table, [key; 32]), socket, 10))
        }

        let (socket_a, addr_a) = bind();
        let (socket_b, _addr_b) = bind();
        let (socket_c, addr_c) = bind();
        let (_dir_a, mut a) = node(vec![addr_c], socket_a, 1);
        let (_dir_b, mut b) = node(vec![addr_a], socket_b, 2);
        let (_dir_c, mut c) = node(vec![], socket_c, 3);

        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        loop {
            let now = crate::block::now_millis();
            a.poll(now).unwrap();
            b.poll(now).unwrap();
            c.poll(now).unwrap();
            let verified_c = b
                .discovery
                .table()
                .get(addr_c)
                .unwrap()
                .is_some_and(|record| record.is_verified());
            if verified_c {
                break;
            }
            assert!(std::time::Instant::now() < deadline, "B never verified C");
        }
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
}

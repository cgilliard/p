//! Wiring the network protocols -- `discovery` (finding peers) and
//! `transfer` (moving blocks) -- to a datagram socket and to the rest of
//! the node.
//!
//! Both protocols are I/O-free state machines; `Node` is the one place
//! that touches a socket. It does so through `Transport`, a minimal
//! "send/receive one datagram" interface: `std::net::UdpSocket`
//! implements it here, and a bare-metal UDP stack can implement it the
//! same way without touching either protocol.
//!
//! `Node` never touches `Chain` directly -- the chain belongs to whoever
//! applies blocks (the miner's thread, in `main`). Finished downloads
//! come out of `poll`; what to announce or fetch next goes in through
//! `command`. `run` connects those to channels for a dedicated network
//! thread. The network reads stored blocks itself, via a `BlockReader`.

#![allow(dead_code)]

use crate::block::Block;
use crate::chain::BlockReader;
use crate::discovery::{Discovery, Outgoing};
use crate::transfer::{self, Transfer};
use crate::txrelay::TxRelay;
use crate::wire::{MAX_PACKET, Message};
use std::net::{SocketAddr, SocketAddrV4};

/// One datagram socket, as `Node` needs it -- the seam between the
/// protocols and whatever UDP stack is underneath.
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
/// never gets to run its ticks.
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

/// What the chain's owner asks the network to do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    /// We have a new tip: tell every peer but `except` (typically the
    /// one we got it from) about it.
    Announce {
        hash: [u8; 32],
        height: u64,
        size: u32,
        except: Option<SocketAddrV4>,
    },
    /// We need this block -- an orphan's missing parent -- and `from` is
    /// likely to have it.
    RequestBlock { hash: [u8; 32], from: SocketAddrV4 },
    /// Our mempool accepted this transaction (encoded): hold it, and
    /// announce it to every peer but `except` (whoever sent it to us).
    AnnounceTx { bytes: Vec<u8>, except: Option<SocketAddrV4> },
    /// This transaction left our mempool (mined, or no longer valid):
    /// stop holding it.
    ForgetTx { id: [u8; 32] },
}

#[derive(Debug)]
pub enum NodeError<E> {
    Peers(crate::peers::Error),
    Transfer(transfer::Error),
    Transport(E),
}

impl<E> From<crate::peers::Error> for NodeError<E> {
    fn from(e: crate::peers::Error) -> Self {
        NodeError::Peers(e)
    }
}

impl<E> From<transfer::Error> for NodeError<E> {
    fn from(e: transfer::Error) -> Self {
        NodeError::Transfer(e)
    }
}

/// `discovery`, `transfer` and `txrelay`, driven over one `Transport`.
pub struct Node<T: Transport> {
    pub discovery: Discovery,
    pub transfer: Transfer,
    pub txrelay: TxRelay,
    /// Transactions downloaded, waiting for `take_transactions`.
    delivered_txs: Vec<(Vec<u8>, SocketAddrV4)>,
    reader: BlockReader,
    /// When set, print every datagram sent and received (except the
    /// individual `CHUNK`s of a block transfer, far too many to read) to
    /// stderr, prefixed with this label -- the node's own port, say. A
    /// debugging aid, off by default.
    pub log: Option<String>,
    transport: T,
    tick_interval_ms: u64,
    next_tick_ms: Option<u64>,
    buf: Vec<u8>,
}

impl<T: Transport> Node<T> {
    /// `tick_interval_ms` is how often both protocols' `tick`s run -- it
    /// bounds how late a timeout or a due probe can be noticed, so keep
    /// it well under every timeout in their configs.
    pub fn new(
        discovery: Discovery,
        transfer: Transfer,
        txrelay: TxRelay,
        reader: BlockReader,
        transport: T,
        tick_interval_ms: u64,
    ) -> Self {
        Node {
            discovery,
            transfer,
            txrelay,
            delivered_txs: Vec::new(),
            reader,
            log: None,
            transport,
            tick_interval_ms,
            next_tick_ms: None,
            // One spare byte past MAX_PACKET, so an oversized datagram
            // shows up as too long (and is rejected) instead of being
            // silently truncated into something that parses.
            buf: vec![0u8; MAX_PACKET + 1],
        }
    }

    fn send_all(&mut self, out: Vec<Outgoing>) {
        // A failed send is just a lost datagram, which both protocols
        // already tolerate (requests time out and are retried).
        for packet in out {
            let result = self.transport.send_to(&packet.bytes, packet.to);
            if let Some(label) = &self.log {
                let message = Message::decode(&packet.bytes);
                if matches!(message, Some(Message::Chunk { .. } | Message::TxChunk { .. })) {
                    continue;
                }
                let what = message.map_or("unparseable packet".to_string(), |m| m.describe());
                match &result {
                    Ok(()) => debug!("[{label}] sent {what} to {}", packet.to),
                    Err(e) => warn!("[{label}] FAILED to send {what} to {}: {e:?}", packet.to),
                }
            }
        }
    }

    /// Act on a request from the chain's owner.
    pub fn command(&mut self, command: Command) -> Result<(), NodeError<T::Error>> {
        let out = match command {
            Command::Announce {
                hash,
                height,
                size,
                except,
            } => {
                self.transfer.announce(hash, height, size, except, &self.discovery)?
            }
            Command::RequestBlock { hash, from } => self.transfer.request_block(hash, from),
            Command::AnnounceTx { bytes, except } => {
                self.txrelay.add(bytes, except, &self.discovery, crate::block::now_millis())?
            }
            Command::ForgetTx { id } => {
                self.txrelay.remove(&id);
                Vec::new()
            }
        };
        self.send_all(out);
        Ok(())
    }

    /// One step: on the first call, `Discovery::start`; afterwards,
    /// handle at most one received datagram, then run both protocols'
    /// ticks if they're due. Returns any blocks that finished
    /// downloading, each with the peer it came from.
    pub fn poll(&mut self, now_ms: u64) -> Result<Vec<(Block, SocketAddrV4)>, NodeError<T::Error>> {
        let Some(next_tick) = self.next_tick_ms else {
            let out = self.discovery.start(now_ms)?;
            self.send_all(out);
            self.next_tick_ms = Some(now_ms + self.tick_interval_ms);
            return Ok(Vec::new());
        };

        let mut delivered = Vec::new();
        if let Some((len, from)) = self.transport.recv_from(&mut self.buf).map_err(NodeError::Transport)? {
            let SocketAddr::V4(from) = from else {
                return Ok(delivered);
            };
            let message = Message::decode(&self.buf[..len]);
            if let Some(label) = &self.log
                && !matches!(message, Some(Message::Chunk { .. } | Message::TxChunk { .. }))
            {
                let what = message.as_ref().map_or(format!("unparseable packet ({len} bytes)"), |m| m.describe());
                debug!("[{label}] recv {what} from {from}");
            }
            if let Some(message) = message {
                let out = match message {
                    Message::GetHosts { .. } | Message::Hosts { .. } => {
                        self.discovery.handle_message(from, &message, len, now_ms)?
                    }
                    Message::TxInv(_) | Message::GetTx { .. } | Message::TxChunk { .. } | Message::GetTxInv { .. } => {
                        let step = self.txrelay.handle(from, &message, &self.discovery, now_ms);
                        self.delivered_txs.extend(step.delivered);
                        step.packets
                    }
                    _ => {
                        let step = self
                            .transfer
                            .handle(from, &message, &self.discovery, &self.reader, now_ms)?;
                        delivered.extend(step.delivered);
                        step.packets
                    }
                };
                self.send_all(out);
            }
        }

        if now_ms >= next_tick {
            let mut out = self.discovery.tick(now_ms)?;
            let step = self.transfer.tick(&self.discovery, &self.reader, now_ms)?;
            out.extend(step.packets);
            delivered.extend(step.delivered);
            let tx_step = self.txrelay.tick(&self.discovery, now_ms)?;
            out.extend(tx_step.packets);
            self.delivered_txs.extend(tx_step.delivered);
            self.send_all(out);
            self.next_tick_ms = Some(now_ms + self.tick_interval_ms);
        }

        if let Some(label) = &self.log {
            for (block, from) in &delivered {
                info!("[{label}] downloaded block #{} from {from}", block.header.height);
            }
            for (bytes, from) in &self.delivered_txs {
                debug!("[{label}] downloaded a transaction ({} bytes) from {from}", bytes.len());
            }
        }
        Ok(delivered)
    }

    /// Transactions downloaded since the last call (encoded, each with the
    /// peer it came from), for the mempool to check.
    pub fn take_transactions(&mut self) -> Vec<(Vec<u8>, SocketAddrV4)> {
        std::mem::take(&mut self.delivered_txs)
    }

    /// `poll` forever until `stop` is set, reading the time from `clock`:
    /// every finished download goes to `deliver`, and every `Command`
    /// waiting on `commands` is acted on between polls.
    /// Blocks go to `deliver`, transactions to `deliver_tx`.
    pub fn run(
        &mut self,
        clock: impl Fn() -> u64,
        stop: &std::sync::atomic::AtomicBool,
        mut deliver: impl FnMut(Block, SocketAddrV4),
        mut deliver_tx: impl FnMut(Vec<u8>, SocketAddrV4),
        commands: &std::sync::mpsc::Receiver<Command>,
    ) -> Result<(), NodeError<T::Error>> {
        while !stop.load(std::sync::atomic::Ordering::Relaxed) {
            while let Ok(command) = commands.try_recv() {
                self.command(command)?;
            }
            for (block, from) in self.poll(clock())? {
                deliver(block, from);
            }
            for (bytes, from) in self.take_transactions() {
                deliver_tx(bytes, from);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::{AcceptOutcome, Chain, DifficultyConfig};
    use crate::discovery;
    use crate::output::Output;
    use crate::peers::PeerTable;
    use crate::storage::Storage;
    use crate::transaction::Transaction;
    use std::net::UdpSocket;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{Duration, Instant};

    struct TempDir(std::path::PathBuf);

    impl TempDir {
        fn new() -> Self {
            static COUNTER: AtomicU64 = AtomicU64::new(0);
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("net-test-{}-{n}", std::process::id()));
            std::fs::create_dir_all(&path).unwrap();
            TempDir(path)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn bind() -> (UdpSocket, SocketAddrV4) {
        let socket = UdpSocket::bind("127.0.0.1:0").unwrap();
        socket.set_read_timeout(Some(Duration::from_millis(2))).unwrap();
        let SocketAddr::V4(local) = socket.local_addr().unwrap() else {
            unreachable!()
        };
        (socket, local)
    }

    fn test_txrelay_config() -> crate::txrelay::Config {
        crate::txrelay::Config {
            chunk_timeout_ms: 200,
            max_retries: 5,
            max_downloads: 16,
            seen_ttl_ms: 60_000,
        }
    }

    struct TestNode {
        _dir: TempDir,
        storage: Storage,
        chain: Chain,
        node: Node<UdpSocket>,
    }

    fn test_node(seeds: Vec<SocketAddrV4>, socket: UdpSocket, key: u8) -> TestNode {
        let dir = TempDir::new();
        let storage = Storage::open(&dir.0).unwrap();
        let mut chain = Chain::open(&storage, DifficultyConfig::for_tests(), 5, None).unwrap();
        chain.skip_proof_checks();
        let table = PeerTable::open(&storage, 100, 3).unwrap();
        let discovery = Discovery::new(
            discovery::Config {
                seeds,
                share_limit: 10,
                probe_interval_ms: 50,
                response_timeout_ms: 500,
            },
            table,
            [key; 32],
        );
        let transfer = Transfer::new(transfer::Config {
            max_block_bytes: crate::block::MAX_BLOCK_BYTES,
            window: 8,
            chunk_timeout_ms: 200,
            max_retries: 5,
            max_downloads: 4,
            peer_height_refresh_ms: 60_000,
        });
        let reader = BlockReader::open(&storage).unwrap();
        let node = Node::new(discovery, transfer, TxRelay::new(test_txrelay_config()), reader, socket, 10);
        TestNode {
            _dir: dir,
            storage,
            chain,
            node,
        }
    }

    impl TestNode {
        /// Poll once, then hand any downloaded block to the chain the way
        /// `main` does, announcing a new tip or asking for a missing parent.
        fn step(&mut self) {
            let delivered = self.node.poll(crate::block::now_millis()).unwrap();
            for (block, from) in delivered {
                let prev = block.header.prev_hash;
                match self.chain.accept_block(block) {
                    Ok(AcceptOutcome::Applied | AcceptOutcome::Reorged { .. }) => {
                        let rtxn = self.storage.read_txn().unwrap();
                        let height = self.chain.height(&rtxn).unwrap().unwrap();
                        let tip = self.chain.tip_hash(&rtxn).unwrap();
                        drop(rtxn);
                        let size = self.node.reader.block_bytes(tip).unwrap().unwrap().len() as u32;
                        self.node
                            .command(Command::Announce {
                                hash: tip,
                                height,
                                size,
                                except: Some(from),
                            })
                            .unwrap();
                    }
                    Ok(AcceptOutcome::Orphaned) => {
                        self.node.command(Command::RequestBlock { hash: prev, from }).unwrap();
                    }
                    _ => {}
                }
            }
        }

        fn tip(&self) -> [u8; 32] {
            let rtxn = self.storage.read_txn().unwrap();
            self.chain.tip_hash(&rtxn).unwrap()
        }
    }

    /// Three real nodes on loopback UDP: B only knows A, A only knows C.
    /// B should end up having verified C itself, purely through A.
    #[test]
    fn hosts_propagate_between_real_udp_nodes() {
        let (socket_a, addr_a) = bind();
        let (socket_b, _addr_b) = bind();
        let (socket_c, addr_c) = bind();
        let mut a = test_node(vec![addr_c], socket_a, 1);
        let mut b = test_node(vec![addr_a], socket_b, 2);
        let mut c = test_node(vec![], socket_c, 3);

        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            a.step();
            b.step();
            c.step();
            let verified_c = b
                .node
                .discovery
                .table()
                .get(addr_c)
                .unwrap()
                .is_some_and(|record| record.is_verified());
            if verified_c {
                break;
            }
            assert!(Instant::now() < deadline, "B never verified C");
        }
    }

    /// A fresh node seeded with a node that already has a chain -- of
    /// blocks big enough to span many chunks -- syncs the whole thing
    /// over real UDP, starting from nothing but the seed address.
    #[test]
    fn a_fresh_node_syncs_a_multi_chunk_chain_over_udp() {
        let (socket_a, addr_a) = bind();
        let (socket_b, _addr_b) = bind();
        let mut a = test_node(vec![], socket_a, 1);
        let mut b = test_node(vec![addr_a], socket_b, 2);

        for height in 0..3u8 {
            let transactions: Vec<Transaction> = (0..60u8)
                .map(|i| {
                    let mut seed = [0u8; 32];
                    seed[0] = height + 1;
                    seed[1] = i;
                    let (_sk, pk) = crate::wots::keygen(&seed);
                    let mut tx = Transaction::new();
                    tx.add_output(Output::new(&pk, 50)).unwrap();
                    tx
                })
                .collect();
            let unproven = a.chain.build_block(&transactions).unwrap();
            let target = unproven.target;
            let proof = crate::prover::Proof::placeholder();
            let mut block = unproven.finish(proof);
            assert!(crate::block::mine_block(&mut block, &target, 100_000));
            assert!(block.to_bytes().len() > crate::wire::CHUNK_LEN);
            a.chain.apply_block(&block).unwrap();
        }

        let deadline = Instant::now() + Duration::from_secs(20);
        while b.tip() != a.tip() {
            a.step();
            b.step();
            assert!(Instant::now() < deadline, "B never caught up to A");
        }
    }

    /// A real signed transaction (one input: about 4 KB, several chunks).
    fn signed_transaction() -> Vec<u8> {
        let keys = crate::keychain::Keychain::test("net relay");
        let (sk, pk) = keys.derive(crate::keychain::KeyId::new(0, 0));
        let mut tx = Transaction::new();
        tx.add_input(&pk, 100).unwrap();
        tx.add_output(keys.output(crate::keychain::KeyId::new(0, 1), 90)).unwrap();
        assert!(tx.sign_input(&pk, &sk));
        tx.to_bytes()
    }

    /// A transaction announced by A reaches B, which relays it on (as the
    /// node does once its mempool accepts it); C, joining later and
    /// knowing only B, gets it from B's mempool sync.
    #[test]
    fn transactions_relay_and_reach_a_late_joiner() {
        let (socket_a, addr_a) = bind();
        let (socket_b, addr_b) = bind();
        let (socket_c, _addr_c) = bind();
        let mut a = test_node(vec![], socket_a, 1);
        let mut b = test_node(vec![addr_a], socket_b, 2);
        let bytes = signed_transaction();
        assert!(bytes.len() > 4 * crate::wire::CHUNK_LEN);

        // Until A and B know each other, then A announces.
        let deadline = Instant::now() + Duration::from_secs(10);
        while a.node.discovery.cookie_from(addr_b).is_none() || b.node.discovery.cookie_from(addr_a).is_none() {
            a.step();
            b.step();
            assert!(Instant::now() < deadline, "A and B never connected");
        }
        a.node.command(Command::AnnounceTx { bytes: bytes.clone(), except: None }).unwrap();

        // B receives it whole, and relays it (as an accepting mempool would).
        let deadline = Instant::now() + Duration::from_secs(10);
        let from = loop {
            a.step();
            b.step();
            if let Some((got, from)) = b.node.take_transactions().pop() {
                assert_eq!(got, bytes);
                break from;
            }
            assert!(Instant::now() < deadline, "B never received the transaction");
        };
        assert_eq!(from, addr_a);
        b.node.command(Command::AnnounceTx { bytes: bytes.clone(), except: Some(from) }).unwrap();
        assert_eq!(b.node.txrelay.held(), 1);

        // C joins knowing only B, and is offered B's transactions.
        let mut c = test_node(vec![addr_b], socket_c, 3);
        let deadline = Instant::now() + Duration::from_secs(10);
        loop {
            a.step();
            b.step();
            c.step();
            if let Some((got, from)) = c.node.take_transactions().pop() {
                assert_eq!((got, from), (bytes.clone(), addr_b));
                break;
            }
            assert!(Instant::now() < deadline, "C never received the transaction");
        }
        // Once received, it isn't fetched again.
        for _ in 0..200 {
            b.step();
            c.step();
        }
        assert!(c.node.take_transactions().is_empty());
        assert_eq!(a.node.take_transactions().len(), 0, "A doesn't fetch back its own transaction");
    }

}

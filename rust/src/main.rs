mod aggregate;
mod block;
mod block_air;
mod bus;
mod chain;
mod chain_rules;
mod chain_step;
mod circuit;
mod cli;
mod contract;
mod discovery;
mod e2e;
mod ext;
mod field;
mod fri;
mod keychain;
mod keytree;
#[macro_use]
mod log;
mod fastsync;
mod mempool;
mod merkle;
mod mnemonic;
mod net;
mod network;
mod node;
mod ntt;
mod output;
mod parallel;
mod peers;
mod policy;
mod poseidon2;
mod poseidon2_air;
mod pow;
mod prover;
mod recovery;
mod recursion;
mod scripture;
mod slate;
mod snapshot;
mod stark;
mod state_circuit;
mod state_tree;
mod statesync;
mod storage;
mod symbolic;
mod transaction;
mod transfer;
mod transcript;
mod txrelay;
mod utxo;
mod wallet;
mod wire;
mod wots;

use block::{Block, now_millis};
use chain::{AcceptOutcome, BlockReader, Chain};
use discovery::Discovery;
use net::Command;
use std::net::SocketAddrV4;
use std::sync::mpsc::{Receiver, Sender};
use peers::PeerTable;
use storage::Storage;

/// How many leading zero bits this driver's starting PoW target has --
/// the knob to turn if the first few blocks feel too fast or too slow.
/// Whole bytes (multiples of 8) are a 256x jump each, too coarse to
/// dial in by hand -- see `pow::max_hash_with_leading_zero_bits`'s
/// docs -- so this is in bits, not bytes: 16 was too fast, 24 too
/// slow, 20 closer but still a bit fast. Only an informed guess, not a
/// calibration: `Chain`'s retargeting (ASERT) corrects for however
/// wrong it actually is as blocks come -- each half-life the chain runs
/// behind (ahead of) schedule halves (doubles) the difficulty -- and
/// this number is independent of `block::INITIAL_MAX_HASH` (which
/// stays fixed and easy, since tests built around it need to mine
/// quickly -- see that constant's docs).
///
/// Main: a ten-minute block is ~5 minutes of proving plus proof of work.
/// 2^23 attempts is about 5 minutes on one thread of a laptop (the node
/// mines on one), so the first blocks come about on time.
const INITIAL_LEADING_ZERO_BITS: u32 = 23;
/// The dev network's (`network`): easier, so proof of work adds little to
/// the proving time that already bounds a block.
const DEV_INITIAL_LEADING_ZERO_BITS: u32 = 20;

/// Retargeting knobs for this driver's actual run (ASERT,
/// `chain::asert`) -- independent of `chain::DifficultyConfig::
/// for_tests`'s own numbers (see that method's docs for why they're
/// deliberately never the same values): the tests use 10 ms blocks.
///
/// Main: a two-day half-life (288 blocks), Bitcoin Cash's.
const HALF_LIFE_MS: u64 = 2 * 24 * 60 * 60 * 1000;
/// Dev: ten minutes, so difficulty follows proving time within a few
/// blocks.
const DEV_HALF_LIFE_MS: u64 = 10 * 60 * 1000;
/// Main: ten minutes, which the reward schedule's eras are counted in
/// (`prover::MAIN_SCHEDULE`).
const TARGET_BLOCK_TIME_MS: u64 = 600_000;
/// The dev network's. Below what proving takes (~80 s a block on dev), so
/// retargeting eases proof of work as far as it goes and blocks come as
/// fast as they're proven.
const DEV_TARGET_BLOCK_TIME_MS: u64 = 10_000;

/// This network's starting difficulty, block time and half-life.
/// Consensus: the chain-proof circuit proves retargeting with these, so
/// changing any means regenerating the network's chain-proof keys (`chain_keys` test)
/// and starting from fresh data directories.
fn leading_zero_bits() -> u32 {
    match network::current() {
        network::Network::Main => INITIAL_LEADING_ZERO_BITS,
        network::Network::Dev => DEV_INITIAL_LEADING_ZERO_BITS,
    }
}

fn target_block_time_ms() -> u64 {
    match network::current() {
        network::Network::Main => TARGET_BLOCK_TIME_MS,
        network::Network::Dev => DEV_TARGET_BLOCK_TIME_MS,
    }
}

fn half_life_ms() -> u64 {
    match network::current() {
        network::Network::Main => HALF_LIFE_MS,
        network::Network::Dev => DEV_HALF_LIFE_MS,
    }
}

/// How many blocks a reorg is ever allowed to unwind in this driver's
/// actual run -- independent of the test suite's own (much smaller)
/// number, same reasoning as the retargeting knobs above. 1000 is a
/// starting point, not a calibration.
const MAX_REORG_DEPTH: u64 = 1000;

/// UDP port discovery listens on when `--port` isn't given.
const DEFAULT_PORT: u16 = 3739;

/// Peer discovery knobs for this driver's actual run (see `discovery`
/// and `peers` for what each one does). Starting points, not
/// calibrations.
const SHARE_LIMIT: u16 = 100;
/// Defaults of `--max-hosts` and `--probe-interval` (seconds): hosts are
/// kept however long they're silent, re-asked every interval, and a full
/// table makes room by evicting the one silent longest (see `peers`).
const DEFAULT_MAX_HOSTS: usize = 256;
const DEFAULT_PROBE_INTERVAL_S: u64 = 60;
/// Default of `--max-per-ip`: how many hosts may share an IP address.
const DEFAULT_MAX_PER_IP: usize = 4;
const RESPONSE_TIMEOUT_MS: u64 = 5_000;
/// Block transfer knobs (see `transfer`). Also starting points.
const CHUNK_WINDOW: u16 = 32;
const CHUNK_TIMEOUT_MS: u64 = 1_000;
const MAX_CHUNK_RETRIES: u32 = 5;
const MAX_DOWNLOADS: usize = 4;
/// How many transactions may be downloading at once.
const MAX_TX_DOWNLOADS: usize = 32;
/// Fast sync: state pieces downloading at once, across all peers.
const MAX_PIECES_IN_FLIGHT: usize = 16;
/// Fast sync: pieces a peer may fail before it's no longer asked.
const MAX_PIECE_STRIKES: u32 = 3;
/// How long a transaction id stays "seen" (not fetched again).
const TX_SEEN_TTL_MS: u64 = 10 * 60_000;
const PEER_HEIGHT_REFRESH_MS: u64 = 60_000;

/// How often the network thread runs both protocols' ticks.
const NETWORK_TICK_MS: u64 = 100;
/// How long one `recv_from` waits before `Node::poll` returns to tick --
/// well under `NETWORK_TICK_MS`, so ticks aren't delayed by it.
const SOCKET_READ_TIMEOUT_MS: u64 = 20;

/// Nonces tried per mining batch. Between batches the miner hands any
/// blocks the network received to the chain, and starts over on a new
/// template if the tip moved -- so this bounds how long it can keep
/// mining on a stale tip.
const MINE_BATCH: u64 = 20_000;

/// This network's retargeting configuration.
fn difficulty_config() -> chain::DifficultyConfig {
    chain::DifficultyConfig {
        pow: match network::current() {
            network::Network::Main => pow::Params::MAIN,
            network::Network::Dev => pow::Params::DEV,
        },
        initial_target: pow::max_hash_with_leading_zero_bits(leading_zero_bits()),
        target_block_time_ms: target_block_time_ms(),
        half_life_ms: half_life_ms(),
        schedule: prover::schedule(),
    }
}

/// This network's genesis block, mined once (see the `mine_genesis` test)
/// and fixed from then on: every node starts its chain from exactly this
/// block, and accepts no other at height 0 (see `Chain::open`). Its body
/// is empty, so its state root is an empty state tree's; its
/// timestamp is the floor every later block's must climb from.
///
/// Each network (`network`) has its own; they differ only in timestamp
/// and nonce (the body, and so the state root, is empty in both).
const GENESIS_STATE_ROOT: &str = "5abee969c7a1566666504b63de10071be7bfcc3b1301802d076b26655c4b7d2f";
const GENESIS_BODY_HASH: &str = "ab928c73b05ea858df784d11d3ff2f21f3048d5a0c8e6b4714c6f52e56fd8871";

/// A network's genesis: timestamp, nonce, and the resulting hash.
struct Genesis {
    timestamp_ms: u64,
    nonce: &'static str,
    hash: &'static str,
}

const MAIN_GENESIS: Genesis = Genesis {
    timestamp_ms: 1_791_423_574_524,
    nonce: "ee25000000000000000000000000000000000000000000000000000000000000",
    hash: "0ae6a56bd798665b288b080eeccfd663f6d50851beed4965082c9d4bc4e8ad64",
};

const DEV_GENESIS: Genesis = Genesis {
    timestamp_ms: 1_791_423_488_875,
    nonce: "f10f000000000000000000000000000000000000000000000000000000000000",
    hash: "4e99d03cd8ccfa7154643b5ccc70055944e76a3408ede52476fe2f28b3690b74",
};

fn genesis() -> &'static Genesis {
    match network::current() {
        network::Network::Main => &MAIN_GENESIS,
        network::Network::Dev => &DEV_GENESIS,
    }
}

fn from_hex32(hex: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("valid hex constant");
    }
    out
}

fn genesis_block() -> Block {
    Block {
        header: block::BlockHeader {
            prev_hash: chain::GENESIS_PARENT_HASH,
            state_root: from_hex32(GENESIS_STATE_ROOT),
            output_count: 0,
            body_hash: from_hex32(GENESIS_BODY_HASH),
            aux_hash: [0; 32],
            version: crate::block::BLOCK_VERSION,
            height: 0,
            timestamp: genesis().timestamp_ms,
            nonce: from_hex32(genesis().nonce),
        },
        body: block::BlockBody::new(),
    }
}

fn default_data_dir(network: network::Network) -> std::path::PathBuf {
    let home = std::env::var("HOME").expect("HOME environment variable must be set");
    let name = match network {
        network::Network::Main => "lmdb",
        network::Network::Dev => "dev",
    };
    std::path::PathBuf::from(home).join(".tabernacle").join(name)
}

/// Command-line options. Hand-parsed -- there are only a few, and this
/// crate takes on no dependencies it doesn't need.
struct Args {
    data_dir: std::path::PathBuf,
    /// `main`, or `dev` (light, insecure proofs for testing).
    network: network::Network,
    port: u16,
    seeds: Vec<SocketAddrV4>,
    mine: bool,
    /// Where to log (default: `tabernacle.log` in the data directory).
    log_file: Option<std::path::PathBuf>,
    log_level: log::Level,
    /// Also log to standard output.
    log_stdout: bool,
    /// The wallet's directory (default: `wallet` in the data directory).
    wallet_dir: Option<std::path::PathBuf>,
    /// Restore the wallet from its 24 backup words, read from stdin.
    recover: bool,
    /// With `--recover`, also read the wallet's passphrase; when creating
    /// a new wallet, protect it with one (read twice).
    passphrase: bool,
    /// Sync a new node block by block from genesis, not by fast sync.
    full_sync: bool,
    /// Fast sync starts this many blocks below the best peer's tip.
    sync_depth: u64,
    /// The most hosts the peer table holds.
    max_hosts: usize,
    /// How often every known host is asked for hosts, in seconds.
    probe_interval_s: u64,
    /// The most hosts in the peer table with one IP address.
    max_per_ip: usize,
    /// No seeds (unless `--seed`s are given), and mine without waiting to
    /// hear a peer: the first node of a new network.
    standalone: bool,
}

/// The seeds a node starts from when no `--seed` is given: the public
/// seeds (Forth nodes, port 3737). `--standalone` starts from none.
const DEFAULT_SEEDS: [&str; 2] = ["159.54.172.190:3737", "146.235.230.124:3737"];

/// Fast sync's default `--sync-depth`: blocks replayed in full after the
/// sync point, and how deep a fast-synced node can reorg at first.
const DEFAULT_SYNC_DEPTH: u64 = 100;

const USAGE: &str = "usage: p [--data-dir PATH] [--port PORT] [--seed IPV4:PORT]... [--no-mine]
         [--log-file PATH] [--log-level trace|debug|info|warn|error] [--log-stdout]
         [--wallet-dir PATH] [--recover] [--passphrase] [--network main|dev]
         [--full-sync] [--sync-depth BLOCKS] [--max-hosts N] [--probe-interval SECONDS]
         [--max-per-ip N] [--standalone]

Without --seed, the node starts from the public seeds; --standalone starts
from none (the first node of a new network: it mines without waiting to hear
a peer).";

fn parse_args() -> Args {
    let mut data_dir = None;
    let mut args = Args {
        data_dir: std::path::PathBuf::new(),
        network: network::Network::Main,
        port: DEFAULT_PORT,
        seeds: Vec::new(),
        mine: true,
        log_file: None,
        log_level: log::Level::Info,
        log_stdout: false,
        wallet_dir: None,
        recover: false,
        passphrase: false,
        full_sync: false,
        sync_depth: DEFAULT_SYNC_DEPTH,
        max_hosts: DEFAULT_MAX_HOSTS,
        probe_interval_s: DEFAULT_PROBE_INTERVAL_S,
        max_per_ip: DEFAULT_MAX_PER_IP,
        standalone: false,
    };
    let mut iter = std::env::args().skip(1);
    while let Some(flag) = iter.next() {
        let mut value = || {
            iter.next().unwrap_or_else(|| {
                eprintln!("{flag} needs a value\n{USAGE}");
                std::process::exit(2);
            })
        };
        match flag.as_str() {
            "--data-dir" => data_dir = Some(value().into()),
            "--network" => {
                let v = value();
                args.network = network::Network::parse(&v).unwrap_or_else(|| {
                    eprintln!("invalid network (expected main or dev): {v}\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--port" => {
                let v = value();
                args.port = v.parse().unwrap_or_else(|_| {
                    eprintln!("invalid port: {v}\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--seed" => {
                let v = value();
                args.seeds.push(v.parse().unwrap_or_else(|_| {
                    eprintln!("invalid seed (expected IPV4:PORT): {v}\n{USAGE}");
                    std::process::exit(2);
                }));
            }
            "--no-mine" => args.mine = false,
            "--standalone" => args.standalone = true,
            "--log-file" => args.log_file = Some(value().into()),
            "--log-level" => {
                let v = value();
                args.log_level = log::Level::parse(&v).unwrap_or_else(|| {
                    eprintln!("invalid log level: {v}\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--log-stdout" => args.log_stdout = true,
            "--wallet-dir" => args.wallet_dir = Some(value().into()),
            "--recover" => args.recover = true,
            "--passphrase" => args.passphrase = true,
            "--full-sync" => args.full_sync = true,
            "--sync-depth" => {
                let v = value();
                args.sync_depth = v.parse().ok().filter(|d| (1..=MAX_REORG_DEPTH / 2).contains(d)).unwrap_or_else(|| {
                    eprintln!("invalid --sync-depth {v} (1 to {})\n{USAGE}", MAX_REORG_DEPTH / 2);
                    std::process::exit(2);
                });
            }
            "--max-hosts" => {
                let v = value();
                args.max_hosts = v.parse().ok().filter(|n| *n >= 1).unwrap_or_else(|| {
                    eprintln!("invalid --max-hosts {v} (at least 1)\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--max-per-ip" => {
                let v = value();
                args.max_per_ip = v.parse().ok().filter(|n| *n >= 1).unwrap_or_else(|| {
                    eprintln!("invalid --max-per-ip {v} (at least 1)\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--probe-interval" => {
                let v = value();
                args.probe_interval_s = v.parse().ok().filter(|n| *n >= 1).unwrap_or_else(|| {
                    eprintln!("invalid --probe-interval {v} (seconds, at least 1)\n{USAGE}");
                    std::process::exit(2);
                });
            }
            "--help" | "-h" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            other => {
                eprintln!("unknown argument: {other}\n{USAGE}");
                std::process::exit(2);
            }
        }
    }
    // Everything that differs between networks reads it from here on.
    network::set(args.network);
    args.data_dir = data_dir.unwrap_or_else(|| default_data_dir(args.network));
    if args.seeds.is_empty() && !args.standalone {
        args.seeds = DEFAULT_SEEDS.iter().map(|s| s.parse().expect("a default seed")).collect();
    }
    args
}

/// The 24 backup words, typed (or piped) on stdin -- never taken as an
/// argument, so they don't end up in the shell's history or the process
/// list. Asks again on a mistake; exits if stdin closes.
fn read_backup_words() -> String {
    use std::io::BufRead;
    let stdin = std::io::stdin();
    let mut lines = stdin.lock().lines();
    loop {
        eprintln!("Enter the wallet's 24 backup words (on one or more lines):");
        let mut words = Vec::new();
        while words.len() < mnemonic::WORDS {
            match lines.next() {
                Some(Ok(line)) => words.extend(line.split_whitespace().map(str::to_string)),
                _ => die("no backup words given"),
            }
        }
        match mnemonic::from_phrase(&words.join(" ")) {
            Ok(_) => return words.join(" "),
            Err(e) => eprintln!("Those words don't restore a wallet: {e}. Try again."),
        }
    }
}

/// A new wallet's backup words, shown once on the terminal (never
/// logged: a log file is no place for them). `seed` shows them again.
fn print_new_wallet_words(wallet: &wallet::Wallet) {
    let (words, passphrase) = match wallet.backup_words() {
        Ok(backup) => backup,
        Err(e) => return eprintln!("failed to read the new wallet's backup words: {e}"),
    };
    println!("A new wallet was created. Its 24 backup words -- write them down, in order, and keep");
    println!("them secret; they're the only way to restore it, and anyone with them can spend it:");
    println!();
    println!("{}", mnemonic::display(&words));
    println!();
    if passphrase {
        println!("Restoring it also takes the passphrase you just chose.");
    }
    println!("(`seed` shows them again.)");
}

/// One line from stdin, after a prompt (without its line ending). Not
/// hidden as it's typed -- there's no terminal handling here.
fn read_line(prompt: &str) -> String {
    use std::io::BufRead;
    eprintln!("{prompt}");
    match std::io::stdin().lock().lines().next() {
        Some(Ok(line)) => line,
        _ => die("stdin closed"),
    }
}

/// 32 fresh random bytes from the OS.
fn random_key() -> [u8; 32] {
    use std::io::Read;
    let mut key = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut key))
        .expect("failed to read /dev/urandom");
    key
}

/// Run the network -- discovery and block transfer -- on its own thread
/// for the life of the process. Returns the channel finished downloads
/// arrive on (each with the peer it came from) and the one to send it
/// `Command`s on.
/// What the network thread hands the node: received blocks and
/// transactions (encoded), each with the peer it came from, and the
/// channel for its commands.
type Network = (
    Receiver<(Block, SocketAddrV4)>,
    Receiver<(Vec<u8>, SocketAddrV4)>,
    Receiver<statesync::Event>,
    Sender<Command>,
    std::sync::Arc<std::sync::atomic::AtomicU64>,
);

fn spawn_network(storage: &Storage, port: u16, seeds: Vec<SocketAddrV4>, max_hosts: usize, max_per_ip: usize, probe_interval_s: u64) -> Network {
    let socket = std::net::UdpSocket::bind(("0.0.0.0", port)).unwrap_or_else(|e| {
        die(&format!("failed to bind UDP port {port}: {e}"));
    });
    socket
        .set_read_timeout(Some(std::time::Duration::from_millis(SOCKET_READ_TIMEOUT_MS)))
        .expect("failed to set socket read timeout");
    let table = PeerTable::open(storage, max_hosts, max_per_ip).expect("failed to open peer table");
    let discovery = Discovery::new(
        discovery::Config {
            seeds,
            share_limit: SHARE_LIMIT,
            probe_interval_ms: probe_interval_s * 1000,
            response_timeout_ms: RESPONSE_TIMEOUT_MS,
        },
        table,
        random_key(),
    );
    let transfer = transfer::Transfer::new(transfer::Config {
        max_block_bytes: block::MAX_BLOCK_BYTES,
        window: CHUNK_WINDOW,
        chunk_timeout_ms: CHUNK_TIMEOUT_MS,
        max_retries: MAX_CHUNK_RETRIES,
        max_downloads: MAX_DOWNLOADS,
        peer_height_refresh_ms: PEER_HEIGHT_REFRESH_MS,
    });
    let reader = BlockReader::open(storage).expect("failed to open block reader");
    let txrelay = txrelay::TxRelay::new(txrelay::Config {
        chunk_timeout_ms: CHUNK_TIMEOUT_MS,
        max_retries: MAX_CHUNK_RETRIES,
        max_downloads: MAX_TX_DOWNLOADS,
        seen_ttl_ms: TX_SEEN_TTL_MS,
    });
    let statesync = statesync::StateSync::new(statesync::Config {
        window: CHUNK_WINDOW,
        chunk_timeout_ms: CHUNK_TIMEOUT_MS,
        max_retries: MAX_CHUNK_RETRIES,
        max_in_flight: MAX_PIECES_IN_FLIGHT,
        max_strikes: MAX_PIECE_STRIKES,
    });
    let state_reader = chain::StateReader::open(storage).expect("failed to open state reader");
    let mut node = net::Node::new(discovery, transfer, txrelay, statesync, reader, state_reader, socket, NETWORK_TICK_MS);
    // Debugging aid for now: log every datagram sent and received,
    // labeled with this node's port so several local nodes' logs are
    // easy to tell apart.
    node.log = Some(format!(":{port}"));
    let peer_height = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(net::NO_PEER_HEIGHT));
    node.peer_height = Some(peer_height.clone());

    let (blocks_tx, blocks_rx) = std::sync::mpsc::channel();
    let (txs_tx, txs_rx) = std::sync::mpsc::channel();
    let (sync_tx, sync_rx) = std::sync::mpsc::channel();
    let (commands_tx, commands_rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        static NEVER_STOP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
        let deliver = |block, from| {
            let _ = blocks_tx.send((block, from));
        };
        let deliver_tx = |bytes, from| {
            let _ = txs_tx.send((bytes, from));
        };
        let deliver_sync = |event| {
            let _ = sync_tx.send(event);
        };
        if let Err(e) = node.run(now_millis, &NEVER_STOP, deliver, deliver_tx, deliver_sync, &commands_rx) {
            error!("network stopped: {e:?}");
        }
    });
    (blocks_rx, txs_rx, sync_rx, commands_tx, peer_height)
}

/// Tell the network to announce our current tip to every peer but
/// `except`.
fn announce_tip(reader: &BlockReader, commands: &Sender<Command>, except: Option<SocketAddrV4>) {
    let Some((height, hash)) = reader.tip().expect("failed to read tip") else {
        return;
    };
    let size = reader
        .block_bytes(hash)
        .expect("failed to read tip block")
        .expect("tip block is stored")
        .len() as u32;
    let _ = commands.send(Command::Announce {
        hash,
        height,
        size,
        except,
    });
}

/// Hand one block received from `from` to the chain, announcing a new
/// tip or asking for a missing parent as needed. Returns whether the tip
/// moved -- compared before and after, since accepting a block can also
/// connect waiting orphans and move the tip further than the block itself.
fn process_one(chain: &mut Chain, reader: &BlockReader, commands: &Sender<Command>, block: Block, from: SocketAddrV4) -> bool {
    let height = block.header.height;
    let prev_hash = block.header.prev_hash;
    let tip_before = reader.tip().expect("failed to read tip");
    match chain.accept_block(block.clone()) {
        Ok(AcceptOutcome::Applied) => {
            info!("received block #{height} from {from}");
            print_block(&block);
        }
        Ok(AcceptOutcome::Reorged { unwound, applied }) => {
            info!("received block #{height} from {from}: reorg, unwound {unwound}, applied {applied}");
            print_block(&block);
        }
        Ok(AcceptOutcome::Orphaned) => {
            info!("received block #{height} from {from}: orphan, asking for its parent");
            let _ = commands.send(Command::RequestBlock { hash: prev_hash, from });
        }
        Ok(AcceptOutcome::StoredAsSideBranch) => info!("received block #{height} from {from}: side branch"),
        Ok(AcceptOutcome::AlreadyKnown) => {}
        Err(e) => info!("rejected block #{height} from {from}: {e}"),
    }
    let tip_moved = reader.tip().expect("failed to read tip") != tip_before;
    if tip_moved {
        announce_tip(reader, commands, Some(from));
    }
    tip_moved
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Convert a Unix timestamp, in **milliseconds**, into a human-readable
/// "YYYY-MM-DD HH:MM:SS.mmm UTC" string. A small, self-contained civil-
/// calendar conversion -- no time zone database needed since this is
/// always UTC, and no new dependency needed for just this. The
/// year/month/day half is Howard Hinnant's `civil_from_days`
/// algorithm (http://howardhinnant.github.io/date_algorithms.html),
/// chosen because it's a well-known, easy-to-verify closed form rather
/// than a loop over "days in this month" by hand.
fn format_timestamp(unix_millis: u64) -> String {
    let unix_secs = unix_millis / 1000;
    let millis = unix_millis % 1000;
    let days = (unix_secs / 86400) as i64;
    let secs_of_day = unix_secs % 86400;
    let (year, month, day) = civil_from_days(days);
    let hour = secs_of_day / 3600;
    let minute = (secs_of_day % 3600) / 60;
    let second = secs_of_day % 60;
    format!("{year:04}-{month:02}-{day:02} {hour:02}:{minute:02}:{second:02}.{millis:03} UTC")
}

/// Days since the Unix epoch (1970-01-01) -> (year, month, day) in the
/// proleptic Gregorian calendar.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = (z - era * 146_097) as u64; // day of era, [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365; // year of era, [0, 399]
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // day of year, [0, 365]
    let mp = (5 * doy + 2) / 153; // month, shifted so March = 0, [0, 11]
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32; // [1, 12]
    let year = if month <= 2 { y + 1 } else { y };
    (year, month, day)
}

/// A 256-bit big-endian integer as an `f64` -- approximate past 2^53,
/// which is fine for display.
fn u256_to_f64(value: [u8; 32]) -> f64 {
    value.iter().fold(0.0, |acc, &byte| acc * 256.0 + byte as f64)
}

/// A hash rate with a readable unit: "812.3 kH/s".
fn format_hash_rate(hashes_per_sec: f64) -> String {
    let units = ["H/s", "kH/s", "MH/s", "GH/s", "TH/s"];
    let mut value = hashes_per_sec;
    let mut unit = 0;
    while value >= 1000.0 && unit < units.len() - 1 {
        value /= 1000.0;
        unit += 1;
    }
    format!("{value:.1} {}", units[unit])
}

/// A duration in seconds with a readable unit: "2.6 s", "4.2 min", "1.5 h".
fn format_duration(secs: f64) -> String {
    if secs < 120.0 {
        format!("{secs:.1} s")
    } else if secs < 7200.0 {
        format!("{:.1} min", secs / 60.0)
    } else {
        format!("{:.1} h", secs / 3600.0)
    }
}

/// This node's mining speed on the block it just mined, and how long a
/// block at `target` would take on average at that speed -- set against
/// the network's intended block time.
fn print_mining_stats(hashes: u64, elapsed: std::time::Duration, target: &[u8; 32]) {
    let secs = elapsed.as_secs_f64().max(1e-9);
    let rate = hashes as f64 / secs;
    let expected_hashes = u256_to_f64(pow::work_for_target(*target));
    info!(
        "  hash rate:   {} ({hashes} hashes in {})",
        format_hash_rate(rate),
        format_duration(secs)
    );
    info!(
        "  expected:    {} per block at this rate (target {})",
        format_duration(expected_hashes / rate),
        format_duration(target_block_time_ms() as f64 / 1000.0)
    );
}

fn print_block(block: &Block) {
    info!("------------------------------------------------------------");
    info!("block #{}", block.header.height);
    info!("  hash:        {}", hex(&block.header.hash()));
    info!("  prev_hash:   {}", hex(&block.header.prev_hash));
    info!(
        "  timestamp:   {} ({})",
        block.header.timestamp,
        format_timestamp(block.header.timestamp)
    );
    info!("  nonce:       {}", hex(&block.header.nonce));
    info!("  state_root:  {}", hex(&block.header.state_root));
    info!("  outputs:     {} in all", block.header.output_count);
    info!("  body_hash:   {}", hex(&block.header.body_hash));
    info!("  inputs:      {}", block.body.inputs.len());
    for commitment in &block.body.inputs {
        info!("    - {}", hex(commitment));
    }
    info!("  outputs:     {}", block.body.outputs.len());
    for commitment in &block.body.outputs {
        info!("    + {}", hex(commitment));
    }
}

/// Set up the log (see `log`): a file (rotated) and, with `--log-stdout`,
/// the terminal too -- which otherwise is told where the log is.
fn start_logging(args: &Args) {
    let file = args.log_file.clone().unwrap_or_else(|| args.data_dir.join("tabernacle.log"));
    let config = log::Config {
        file: Some(file.clone()),
        stdout: args.log_stdout,
        colors: false,
        level: args.log_level,
        header: Some(format!("tabernacle node log (port {})", args.port)),
        ..log::Config::default()
    };
    if let Err(e) = log::init(config) {
        eprintln!("failed to open log file {}: {e}", file.display());
        std::process::exit(1);
    }
    if !args.log_stdout {
        println!("Logging to {} (level {}).", file.display(), args.log_level);
    }
}

/// Log a fatal error, say so on the terminal too, and exit.
fn die(message: &str) -> ! {
    fatal!("{message}");
    eprintln!("{message}");
    std::process::exit(1);
}

fn main() {
    let args = parse_args();
    let path = args.data_dir.clone();
    // `Storage::open` would transparently create-or-load either way
    // (LMDB behaves the same regardless), but checking first lets us
    // say which one actually happened.
    let is_new = !path.exists();
    start_logging(&args);
    if is_new {
        info!("No existing chain found at {} -- creating a new one.", path.display());
    } else {
        info!("Found an existing chain at {} -- loading it.", path.display());
    }

    let storage = Storage::open_with_map_size(&path, storage::NODE_MAP_SIZE).expect("failed to open storage");
    if args.network != network::Network::Main {
        info!("Network: {} (light, insecure proofs -- for testing only)", args.network.name());
    }
    if !scripture::check() {
        die("the embedded text (data/akjv.txt.gz) isn't the pinned one: this build is broken");
    }
    let genesis = genesis_block();
    assert_eq!(hex(&genesis.header.hash()), self::genesis().hash, "genesis constants are inconsistent");
    info!("Genesis block: {}", self::genesis().hash);
    let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap_or_else(|e| {
        let hint = match e {
            chain::Error::WrongGenesis => " (its data is from a chain with a different genesis block -- delete it, or use another --data-dir)",
            chain::Error::OldStorage => " (delete it, or use another --data-dir)",
            _ => "",
        };
        die(&format!("failed to open chain at {}: {e}{hint}", path.display()));
    });
    // Every block after genesis carries its parent's chain proof.
    chain.require_chain_proofs(chain_step::consensus_verifier());
    let fresh = {
        let rtxn = storage.read_txn().expect("failed to open read transaction");
        chain.height(&rtxn).expect("failed to read chain height").unwrap_or(0) == 0
    };

    {
        let rtxn = storage.read_txn().expect("failed to open read transaction");
        match chain.height(&rtxn).expect("failed to read chain height") {
            Some(height) => {
                let tip = chain.tip_hash(&rtxn).expect("failed to read tip hash");
                info!("Resuming at height {height}, tip {}.", hex(&tip));
            }
            None => info!("Starting from genesis."),
        }
    }

    if args.seeds.is_empty() {
        info!("Listening on UDP port {} (standalone: no seeds).", args.port);
    } else {
        let seeds: Vec<String> = args.seeds.iter().map(|s| s.to_string()).collect();
        info!("Listening on UDP port {}, seeds: {}.", args.port, seeds.join(", "));
    }
    let standalone = args.standalone;
    let (received, received_txs, sync_events, commands, peer_height) = spawn_network(&storage, args.port, args.seeds, args.max_hosts, args.max_per_ip, args.probe_interval_s);
    let fast_sync = (fresh && !args.full_sync).then(|| fastsync::FastSync::new(args.sync_depth, &commands));
    let reader = BlockReader::open(&storage).expect("failed to open block reader");
    let peer_table = PeerTable::open(&storage, args.max_hosts, args.max_per_ip).expect("failed to open peer table");
    let wallet_dir = args.wallet_dir.clone().unwrap_or_else(|| path.join("wallet"));
    // A wallet made just now (not restored) shows its backup words once.
    let created = !args.recover && !wallet_dir.join("data.mdb").exists();
    let wallet = if args.recover {
        let words = read_backup_words();
        let passphrase = if args.passphrase { read_line("The wallet's passphrase:") } else { String::new() };
        let wallet = wallet::Wallet::restore_from_words(&wallet_dir, &words, &passphrase)
            .unwrap_or_else(|e| die(&format!("failed to restore the wallet at {}: {e}", wallet_dir.display())));
        println!("Restoring the wallet: it will scan the chain once this node has caught up with its peers (`status` shows progress).");
        wallet
    } else if args.passphrase {
        if wallet_dir.join("data.mdb").exists() {
            die("--passphrase: the wallet already exists (a passphrase is set when a wallet is created, or with --recover)");
        }
        let passphrase = read_line("A passphrase for the new wallet (it will be needed, with the backup words, to restore it):");
        if passphrase.is_empty() || read_line("The passphrase again:") != passphrase {
            die("the passphrases were empty or didn't match");
        }
        wallet::Wallet::create_with_passphrase(&wallet_dir, &passphrase)
            .unwrap_or_else(|e| die(&format!("failed to create the wallet at {}: {e}", wallet_dir.display())))
    } else {
        wallet::Wallet::open(&wallet_dir).unwrap_or_else(|e| die(&format!("failed to open wallet at {}: {e}", wallet_dir.display())))
    };
    info!("Wallet: {}", wallet_dir.display());
    if created {
        info!("wallet: created a new wallet (its backup words were shown on the terminal, not logged)");
        print_new_wallet_words(&wallet);
    }

    // The node runs here; the command line reads the terminal on its own
    // thread and sends it requests.
    let (requests_tx, requests) = std::sync::mpsc::channel();
    std::thread::spawn(move || cli::run(requests_tx));
    let mut node = node::Node::new(chain, reader, received, received_txs, commands, peer_table, wallet, args.mine, requests);
    node.chain_prover = std::sync::Arc::new(std::sync::Mutex::new(chain_step::ChainProver::new(difficulty_config(), prover::tree())));
    node.peer_height = peer_height;
    node.standalone = standalone;
    node.fast_sync = fast_sync;
    node.sync_events = Some(sync_events);
    node.run();
    std::process::exit(0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::mine_block;

    fn hex32(bytes: &[u8; 32]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn temp_storage(name: &str) -> (std::path::PathBuf, Storage) {
        let dir = std::env::temp_dir().join(format!("main-test-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let storage = Storage::open(&dir).unwrap();
        (dir, storage)
    }

    #[test]
    fn the_genesis_block_is_valid_and_matches_its_recorded_hash() {
        let genesis = genesis_block();
        assert_eq!(hex32(&genesis.header.hash()), self::genesis().hash);
        // Structure only: genesis is exempt from the proof check (see
        // `Chain`'s `block_is_valid`) -- its empty body claims no reward.
        assert!(genesis.validate_structure(&difficulty_config().initial_target, &difficulty_config().pow));
    }

    /// Opening an empty chain applies genesis; reopening it is fine.
    #[test]
    fn opening_an_empty_chain_starts_it_at_genesis() {
        let (dir, storage) = temp_storage("genesis-open");
        let genesis = genesis_block();
        let chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        let rtxn = storage.read_txn().unwrap();
        assert_eq!(chain.tip_hash(&rtxn).unwrap(), genesis.header.hash());
        assert_eq!(chain.height(&rtxn).unwrap(), Some(0));
        drop(rtxn);
        drop(chain);
        Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Data from a chain with some other first block refuses to open.
    #[test]
    fn data_from_a_different_genesis_is_refused() {
        let (dir, storage) = temp_storage("genesis-other");
        let mut other = Chain::open(&storage, chain::DifficultyConfig::for_tests(), MAX_REORG_DEPTH, None).unwrap();
        other.skip_proof_checks();
        let unproven = other.build_block(&[]).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut first = unproven.finish(proof);
        assert!(mine_block(&mut first, &target, 100_000, &pow::Params::TEST));
        other.apply_block(&first).unwrap();
        drop(other);

        let result = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis_block()));
        assert!(matches!(result, Err(chain::Error::WrongGenesis)));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Mines a fresh genesis block at this network's starting difficulty
    /// and prints its header fields, for pasting into `genesis_block`.
    /// Run once, on purpose, with
    /// `cargo test --release -- --ignored --nocapture mine_genesis`.
    #[test]
    #[ignore]
    fn mine_genesis() {
        let dir = std::env::temp_dir().join(format!("genesis-{}", std::process::id()));
        let storage = Storage::open(&dir).unwrap();
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, None).unwrap();
        let unproven = chain.build_block(&[]).unwrap();
        let target = unproven.target;
        let proof = prover::Proof::placeholder();
        let mut block = unproven.finish(proof);
        while !mine_block(&mut block, &target, MINE_BATCH, &difficulty_config().pow) {
            block.header.timestamp = now_millis();
        }
        let h = &block.header;
        println!("GENESIS_TIMESTAMP_MS = {}", h.timestamp);
        println!("GENESIS_STATE_ROOT = {}", hex32(&h.state_root));
        println!("GENESIS_BODY_HASH = {}", hex32(&h.body_hash));
        println!("GENESIS_NONCE = {}", hex32(&h.nonce));
        println!("GENESIS_HASH = {}", hex32(&h.hash()));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The chain-proof circuits' verifying keys for this network: mine a
    /// real first block on its genesis, prove the genesis's chain proof and
    /// the first block's, and print both circuits' caps -- run after any
    /// change to the circuits, the genesis, or the tree keys, then update
    /// `chain_step`'s `GENESIS_CAP` / `STEP_CAP` (or `DEV_...`). Slow:
    /// `[NETWORK=dev] cargo test --release -- --ignored --nocapture chain_keys`.
    #[test]
    #[ignore]
    fn chain_keys() {
        let (dir, storage) = temp_storage("chain-keys");
        let genesis = genesis_block();
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        let mut chain_prover = chain_step::ChainProver::new(difficulty_config(), prover::tree());
        let g_proof = chain_prover.prove(&chain.chain_proof_inputs(genesis.header.hash()).unwrap(), || None, [1; 32]).unwrap();
        let (_, pk) = wots::keygen(&[5; 32]);
        let mut reward = transaction::Transaction::new();
        reward.add_output(output::Output::new(&pk, prover::REWARD)).unwrap();
        let txs = [reward];
        let unproven = chain.build_block(&txs).unwrap();
        let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
        let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &txs, &unproven.plan, [2; 32]).unwrap();
        let mut block = unproven.finish_with_chain_proof(proof, g_proof);
        block.header.timestamp = block.header.timestamp.max(min_timestamp);
        while !mine_block(&mut block, &target, MINE_BATCH, &difficulty_config().pow) {
            block.header.timestamp = now_millis();
        }
        let hash = block.header.hash();
        chain.apply_block(&block).unwrap();
        let p1 = chain_prover.prove(&chain.chain_proof_inputs(hash).unwrap(), || None, [3; 32]).unwrap();
        let keys = chain_prover.keys().unwrap();
        let verifier = chain_step::ChainVerifier::of(&keys, prover::tree());
        assert!(verifier.verify(&chain.chain_proof_inputs(hash).unwrap().tip, &p1));
        let prefix = if network::current() == network::Network::Dev { "DEV_" } else { "" };
        println!("const {prefix}GENESIS_CAP: &str = \"{}\";", chain_step::cap_to_hex(&verifier.genesis_cap));
        println!("const {prefix}STEP_CAP: &str = \"{}\";", chain_step::cap_to_hex(&verifier.step_cap));
        let consensus = chain_step::consensus_verifier();
        let _ = std::fs::remove_dir_all(&dir);
        assert!(
            consensus.genesis_cap == verifier.genesis_cap && consensus.step_cap == verifier.step_cap,
            "the chain-proof key constants are stale: update them to the above"
        );
    }

    /// Test blocks for the Forth validator (`forth/tests/fixtures/<network>/`):
    /// a real chain of genesis, block 1 (its reward to a known key) and block
    /// 2 (its reward, and one transaction spending block 1's output: one
    /// input, two outputs, a fee), with every block's proofs and the chain
    /// proof that block 2's child would carry -- plus each block's tip, its
    /// target, and its root proof's challenge and product, and how long each
    /// step took. Slow (about 25 minutes on main); rerun after any consensus
    /// change: `[NETWORK=dev] cargo test --release -- --ignored --nocapture forth_fixtures`.
    #[test]
    #[ignore]
    fn forth_fixtures() {
        let net = if network::current() == network::Network::Dev { "dev" } else { "main" };
        let out = format!("{}/../forth/tests/fixtures/{net}", env!("CARGO_MANIFEST_DIR"));
        std::fs::create_dir_all(&out).unwrap();
        let start = std::time::Instant::now();
        let mut times = String::new();
        let mut timed = |what: &str, since: std::time::Instant| times += &format!("TIME {what} {:.1}\n", since.elapsed().as_secs_f64());
        let (dir, storage) = temp_storage("forth-fixtures");
        let genesis = genesis_block();
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        let mut chain_prover = chain_step::ChainProver::new(difficulty_config(), prover::tree());
        let s = std::time::Instant::now();
        let mut chain_proof = chain_prover.prove(&chain.chain_proof_inputs(genesis.header.hash()).unwrap(), || None, [1; 32]).unwrap();
        timed("genesis_chain_proof_with_keys", s);
        let key = |k: u8| wots::keygen(&[k; 32]);
        let (sk1, pk1) = key(5);
        const FEE: u64 = 10_000;
        let pay = 600_000_000;
        let mut info = String::new();
        let j = |v: &[poseidon2::BabyBear]| v.iter().map(|x| x.value().to_string()).collect::<Vec<_>>().join(" ");
        let h = |b: &[u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let tip_line = |name: &str, t: &chain_step::Tip| {
            format!(
                "TIP {name} hash {} height {} timestamp {} target {} state_root {} output_count {} anchor {} work {}\n",
                h(&t.hash), t.height, t.timestamp, h(&t.target), h(&t.state_root), t.output_count, t.anchor_timestamp, h(&t.work)
            )
        };
        info += &tip_line("0", &chain.chain_proof_inputs(genesis.header.hash()).unwrap().tip);
        std::fs::write(format!("{out}/block0.bin"), genesis.to_bytes()).unwrap();
        let mut parent = genesis.header;
        for height in 1..=2u64 {
            let reward_amount = prover::schedule().reward(height).unwrap();
            let mut txs = Vec::new();
            let mut reward = transaction::Transaction::new();
            if height == 1 {
                reward.add_output(output::Output::new(&pk1, reward_amount)).unwrap();
                txs.push(reward);
            } else {
                reward.add_output(output::Output::new(&key(8).1, reward_amount + FEE)).unwrap();
                let mut spend = transaction::Transaction::new();
                spend.add_input(&pk1, prover::REWARD).unwrap();
                spend.add_output(output::Output::new(&key(6).1, pay)).unwrap();
                spend.add_output(output::Output::new(&key(7).1, prover::REWARD - pay - FEE)).unwrap();
                assert!(spend.sign_input(&pk1, &sk1));
                txs.push(reward);
                txs.push(spend);
            }
            let unproven = chain.build_block(&txs).unwrap();
            let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
            let s = std::time::Instant::now();
            let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &txs, &unproven.plan, [2 + height as u8; 32]).unwrap();
            timed(&format!("block{height}_proof"), s);
            let mut block = unproven.finish_with_chain_proof(proof, chain_proof);
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            let s = std::time::Instant::now();
            while !mine_block(&mut block, &target, MINE_BATCH, &difficulty_config().pow) {
                block.header.timestamp = now_millis();
            }
            timed(&format!("block{height}_mining"), s);
            let parent_state = (parent.state_root, parent.output_count);
            let s = std::time::Instant::now();
            assert!(block.validate(&target, &difficulty_config().pow, parent_state, reward_amount));
            timed(&format!("block{height}_rust_validate"), s);
            let node = prover::block_root(&block.body.proof, &block.body.inputs, &block.body.outputs, &block.body.nonces, &block.state_change(parent_state), height as u32).unwrap();
            info += &format!(
                "BLOCK {height} target {} reward {reward_amount} inputs {} outputs {} challenge {} product {} len {} proof_len {} chain_proof_len {}\n",
                h(&target), block.body.inputs.len(), block.body.outputs.len(), j(&node.challenge), j(&node.product.0),
                block.to_bytes().len(), block.body.proof.as_bytes().len(), block.body.chain_proof.len()
            );
            let hash = block.header.hash();
            chain.apply_block(&block).unwrap();
            let s = std::time::Instant::now();
            chain_proof = chain_prover.prove(&chain.chain_proof_inputs(hash).unwrap(), || None, [9 + height as u8; 32]).unwrap();
            timed(&format!("block{height}_chain_proof"), s);
            info += &tip_line(&height.to_string(), &chain.chain_proof_inputs(hash).unwrap().tip);
            std::fs::write(format!("{out}/block{height}.bin"), block.to_bytes()).unwrap();
            parent = block.header;
        }
        std::fs::write(format!("{out}/chain2.bin"), &chain_proof).unwrap();
        timed("total", start);
        std::fs::write(format!("{out}/info.txt"), format!("NETWORK {net}\n{info}{times}")).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A data directory for a Rust node the Forth validator syncs from
    /// (`forth/scripts/test_net.sh`): `forth/tmp/peer-<network>`, holding the
    /// fixture chain's genesis, block 1, and the 2b/3b branch
    /// (`forth_fixtures`, `forth_fork_fixtures`) -- so 3b is its tip. Quick:
    /// `cargo test --release -- --ignored forth_peer_data`.
    #[test]
    #[ignore]
    fn forth_peer_data() {
        let net = if network::current() == network::Network::Dev { "dev" } else { "main" };
        let fixtures = format!("{}/../forth/tests/fixtures/{net}", env!("CARGO_MANIFEST_DIR"));
        let dir = std::path::PathBuf::from(format!("{}/../forth/tmp/peer-{net}", env!("CARGO_MANIFEST_DIR")));
        let _ = std::fs::remove_dir_all(&dir);
        let read = |name: &str| block::Block::from_bytes(&std::fs::read(format!("{fixtures}/{name}")).unwrap()).unwrap();
        let storage = Storage::open_with_map_size(&dir, storage::NODE_MAP_SIZE).unwrap();
        let genesis = genesis_block();
        assert_eq!(genesis.to_bytes(), read("block0.bin").to_bytes(), "the fixtures are from another genesis");
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&genesis)).unwrap();
        chain.require_chain_proofs(chain_step::consensus_verifier());
        for name in ["block1.bin", "block2b.bin", "block3b.bin"] {
            chain.apply_block(&read(name)).unwrap();
        }
    }

    /// The Forth wallet's key vectors (`forth/tests/wallet.fam`): for the
    /// backup words of entropy 0x7f..7f, the seed with a passphrase, and
    /// the seed's view key, key seed and public key hash at 0/7. Quick:
    /// `cargo test --release -- --ignored --nocapture forth_wallet_vectors`.
    #[test]
    #[ignore]
    fn forth_wallet_vectors() {
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02X}")).collect::<String>();
        let entropy = [0x7f; 32];
        println!("words      {}", mnemonic::to_phrase(&entropy));
        println!("passphrase {}", hex(&mnemonic::seed_from(&entropy, "correct horse")));
        let keychain = keychain::Keychain::from_seed(entropy);
        println!("view key   {}", hex(&keychain.view_key().0));
        let id = keychain::KeyId::new(0, 7);
        let key_seed = poseidon2::hash_bytes_32(&[b"tabernacle-keychain-v1".as_slice(), &entropy, &id.to_bytes()].concat());
        println!("key seed   {}", hex(&key_seed));
        println!("pk hash    {}", hex(&poseidon2::digest_to_bytes(keychain.public_key(id).hash())));
        // An output of 5.000000123 coins to 0/7, sealed for recovery.
        let commitment = keychain.output(id, 5_000_000_123).commitment();
        println!("commitment {}", hex(&commitment));
        println!("nonce      {}", hex(&recovery::seal(&keychain.view_key(), &commitment, 7, 5_000_000_123)));
    }

    /// A transaction for the Forth mempool's tests (`forth/tests/txvec.fam`):
    /// two inputs -- a one-time key's, and leaf 2 of a height-3 key tree's --
    /// and two outputs, signed; written as a Forth table, with its id and its
    /// inputs' and outputs' commitments. Quick:
    /// `cargo test --release -- --ignored --nocapture forth_tx_vectors`.
    #[test]
    #[ignore]
    fn forth_tx_vectors() {
        let keys = keychain::Keychain::from_seed([0x7f; 32]);
        let (sk1, pk1) = keys.derive(keychain::KeyId::new(0, 3));
        let tree = keytree::KeyTree::generate(&[0x42; 32], 3);
        let (sk2, pk2) = tree.leaf(2);
        let mut tx = transaction::Transaction::new();
        tx.add_input(&pk1, 7_000_000_000).unwrap();
        tx.add_tree_input(&pk2, tree.proof(2), 3_000_000_123).unwrap();
        tx.add_output(keys.output(keychain::KeyId::new(0, 9), 6_000_000_000)).unwrap();
        tx.add_output(keys.output(keychain::KeyId::new(0, 10), 3_999_000_123)).unwrap();
        assert!(tx.sign_input(&pk1, &sk1) && tx.sign_input(&pk2, &sk2) && tx.verify());
        let bytes = tx.to_bytes();
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02X}")).collect::<String>();
        let mut out = String::from("\\ Made by the Rust node: `cargo test --release -- --ignored forth_tx_vectors`.\n");
        out += &format!("\\ txv ( -- a n ): a signed transaction, {} bytes: a one-time key's input and\n\\ a key tree's (leaf 2 of 8), two outputs.\n", bytes.len());
        out += ": txv ( -- a n )\n97020000 ,   \\ auipc t0,0\n93824201 ,   \\ addi t0,t0,20\n1301C1FF ,   \\ addi sp,sp,-4\n23205100 ,   \\ sw t0,0(sp)\n";
        let mut padded = bytes.clone();
        padded.resize(bytes.len().div_ceil(4) * 4, 0);
        let off = padded.len() + 4;
        let jal = 0x6Fu32 | (((off as u32 >> 1) & 0x3FF) << 21) | (((off as u32 >> 11) & 1) << 20) | (((off as u32 >> 12) & 0xFF) << 12);
        out += &format!("{} ,\n", hex(&jal.to_le_bytes()));
        for w in padded.chunks(4) {
            out += &format!("{} ,\n", hex(w));
        }
        out += &format!("{:X} lit\n;\n", bytes.len());
        out += &format!("\\ id {}\n", hex(&tx.id()));
        for i in &tx.inputs {
            out += &format!("\\ input commitment {}\n", hex(&i.commitment()));
        }
        for o in &tx.outputs {
            out += &format!("\\ output commitment {}\n", hex(&o.commitment()));
        }
        std::fs::write(format!("{}/../forth/tests/txvec.fam", env!("CARGO_MANIFEST_DIR")), out).unwrap();
        // A second: policy spends -- branch 0 (2 of 3 keys, one of them a key
        // tree's, a hashlock and a height lock) of a two-branch policy, and a
        // REBIND branch naming an output -- and a key spend.
        let key_id = |pk: &wots::PublicKey| keytree::KeyProof::one_time().key_id(pk);
        let (ska, pka) = keys.derive(keychain::KeyId::new(0, 20));
        let (skc, pkc) = keys.derive(keychain::KeyId::new(0, 22));
        let (skr, pkr) = keys.derive(keychain::KeyId::new(0, 23));
        let (skk, pkk) = keys.derive(keychain::KeyId::new(0, 24));
        let tree2 = keytree::KeyTree::generate(&[0x43; 32], 3);
        let (skb, pkb) = tree2.leaf(5);
        let preimage = poseidon2::digest_to_bytes(keys.public_key(keychain::KeyId::new(0, 30)).hash());
        let branch0 = policy::Branch { threshold: 2, keys: vec![key_id(&pka), tree2.id(), key_id(&pkc)], after_height: 2, after_age: 1, hashlock: policy::hashlock(&preimage), rebind: None };
        let branch1 = policy::Branch { threshold: 1, keys: vec![key_id(&pkk)], after_height: 0, after_age: 0, hashlock: None, rebind: None };
        let pol = policy::Policy { branches: vec![branch0.clone(), branch1] };
        let rbranch = policy::Branch { threshold: 1, keys: vec![key_id(&pkr)], after_height: 0, after_age: 0, hashlock: None, rebind: Some(1) };
        let mut tx2 = transaction::Transaction::new();
        let out_a = keys.output(keychain::KeyId::new(0, 40), 4_000_000_000);
        let out_b = keys.output(keychain::KeyId::new(0, 41), 2_999_000_000);
        tx2.add_policy_input(branch0, 0, pol.path(0).into_iter().map(poseidon2::digest_to_bytes).collect(), Some(preimage), 3_000_000_000).unwrap();
        tx2.add_rebind_input(rbranch, 0, vec![], None, 2_000_000_000, 2, vec![out_a.commitment()]).unwrap();
        tx2.add_input(&pkk, 2_000_000_000).unwrap();
        tx2.add_output(out_a.clone()).unwrap();
        tx2.add_output(out_b).unwrap();
        let commit_of = |tx: &transaction::Transaction, rebinds: bool| tx.inputs.iter().find(|i| i.rebinds() == rebinds && i.key().is_none()).unwrap().commitment();
        let (rc, pc) = (commit_of(&tx2, true), commit_of(&tx2, false));
        assert!(tx2.sign_policy_input(&rc, 0, &pkr, keytree::KeyProof::one_time(), &skr));
        assert!(tx2.sign_policy_input(&pc, 0, &pka, keytree::KeyProof::one_time(), &ska));
        assert!(tx2.sign_policy_input(&pc, 1, &pkb, tree2.proof(5), &skb));
        assert!(tx2.sign_input(&pkk, &skk) && tx2.verify());
        let _ = (&skc, &pkc);
        let bytes = tx2.to_bytes();
        let mut out = std::fs::read_to_string(format!("{}/../forth/tests/txvec.fam", env!("CARGO_MANIFEST_DIR"))).unwrap();
        out += &format!("\n\\ txv2 ( -- a n ): {} bytes: a policy spend (branch 0 of 2: 2 of 3 keys, one a key\n\\ tree's; a hashlock; locked to height 2, age 1), a REBIND spend naming the\n\\ first output, and a key spend; two outputs.\n", bytes.len());
        out += ": txv2 ( -- a n )\n97020000 ,   \\ auipc t0,0\n93824201 ,   \\ addi t0,t0,20\n1301C1FF ,   \\ addi sp,sp,-4\n23205100 ,   \\ sw t0,0(sp)\n";
        let mut padded = bytes.clone();
        padded.resize(bytes.len().div_ceil(4) * 4, 0);
        let off = padded.len() + 4;
        let jal = 0x6Fu32 | (((off as u32 >> 1) & 0x3FF) << 21) | (((off as u32 >> 11) & 1) << 20) | (((off as u32 >> 12) & 0xFF) << 12);
        out += &format!("{} ,\n", hex(&jal.to_le_bytes()));
        for w in padded.chunks(4) {
            out += &format!("{} ,\n", hex(w));
        }
        out += &format!("{:X} lit\n;\n", bytes.len());
        out += &format!("\\ id {}\n", hex(&tx2.id()));
        for i in &tx2.inputs {
            out += &format!("\\ input commitment {}\n", hex(&i.commitment()));
        }
        for o in &tx2.outputs {
            out += &format!("\\ output commitment {}\n", hex(&o.commitment()));
        }
        std::fs::write(format!("{}/../forth/tests/txvec.fam", env!("CARGO_MANIFEST_DIR")), out).unwrap();
    }

    /// Fast sync for the Forth validator's tests (`forth/tests/fixtures/<network>/`,
    /// reading `forth_fixtures`' chain): the state as of blocks 1 and 2, as
    /// this node serves it, in `snap1.bin` and `snap2.bin` -- the sync point
    /// (target, window start as a big-endian u64, work), then each piece in
    /// the order a download takes them: level, index and length (big-endian
    /// u32s), the bytes, zeros to a multiple of 4. Quick (no proving):
    /// `[NETWORK=dev] cargo test --release -- --ignored --nocapture forth_snapshot_fixtures`.
    #[test]
    #[ignore]
    fn forth_snapshot_fixtures() {
        let net = if network::current() == network::Network::Dev { "dev" } else { "main" };
        let out = format!("{}/../forth/tests/fixtures/{net}", env!("CARGO_MANIFEST_DIR"));
        let read = |name: &str| block::Block::from_bytes(&std::fs::read(format!("{out}/{name}")).unwrap()).unwrap();
        let blocks = [read("block0.bin"), read("block1.bin"), read("block2.bin")];
        let (dir, storage) = temp_storage("forth-snapshot-fixtures");
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&blocks[0])).unwrap();
        chain.apply_block(&blocks[1]).unwrap();
        chain.apply_block(&blocks[2]).unwrap();
        let reader = chain::StateReader::open(&storage).unwrap();
        for k in [1, 2] {
            let header = &blocks[k].header;
            let hash = header.hash();
            let point = reader.sync_point(hash).unwrap().unwrap();
            let mut bytes = Vec::new();
            bytes.extend_from_slice(&point.target);
            bytes.extend_from_slice(&point.anchor_timestamp.to_be_bytes());
            bytes.extend_from_slice(&point.work);
            let mut plan = snapshot::Plan::new(header.state_root, header.output_count);
            while let Some(piece) = plan.next() {
                let data = reader.piece(hash, piece.level, piece.index).unwrap().unwrap();
                assert!(plan.accept(&piece, &data));
                for v in [piece.level as u32, piece.index as u32, data.len() as u32] {
                    bytes.extend_from_slice(&v.to_be_bytes());
                }
                bytes.extend_from_slice(&data);
                bytes.resize(bytes.len().next_multiple_of(4), 0);
            }
            std::fs::write(format!("{out}/snap{k}.bin"), bytes).unwrap();
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A side branch for the Forth validator's reorganization tests
    /// (`forth/tests/fixtures/<network>/`, next to `forth_fixtures`' chain,
    /// which it reads): blocks 2b and 3b on block 1 -- each just a reward, to
    /// other keys -- so the branch outweighs block 2. Plus 3b's chain proof.
    /// Slow (about 25 minutes on main):
    /// `[NETWORK=dev] cargo test --release -- --ignored --nocapture forth_fork_fixtures`.
    #[test]
    #[ignore]
    fn forth_fork_fixtures() {
        let net = if network::current() == network::Network::Dev { "dev" } else { "main" };
        let out = format!("{}/../forth/tests/fixtures/{net}", env!("CARGO_MANIFEST_DIR"));
        let read = |name: &str| block::Block::from_bytes(&std::fs::read(format!("{out}/{name}")).unwrap()).unwrap();
        let (block0, block1, block2) = (read("block0.bin"), read("block1.bin"), read("block2.bin"));
        let start = std::time::Instant::now();
        let mut times = String::new();
        let mut timed = |what: &str, since: std::time::Instant| times += &format!("TIME {what} {:.1}\n", since.elapsed().as_secs_f64());
        let (dir, storage) = temp_storage("forth-fork-fixtures");
        let mut chain = Chain::open(&storage, difficulty_config(), MAX_REORG_DEPTH, Some(&block0)).unwrap();
        chain.apply_block(&block1).unwrap();
        let mut chain_prover = chain_step::ChainProver::new(difficulty_config(), prover::tree());
        // Block 1's chain proof: what block 2 carries. (The prover derives
        // its keys from block 1's inputs, the chain's second block.)
        let mut chain_proof = block2.body.chain_proof.clone();
        let h = |b: &[u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let j = |v: &[poseidon2::BabyBear]| v.iter().map(|x| x.value().to_string()).collect::<Vec<_>>().join(" ");
        let tip_line = |name: &str, t: &chain_step::Tip| {
            format!(
                "TIP {name} hash {} height {} timestamp {} target {} state_root {} output_count {} anchor {} work {}\n",
                h(&t.hash), t.height, t.timestamp, h(&t.target), h(&t.state_root), t.output_count, t.anchor_timestamp, h(&t.work)
            )
        };
        let mut info = String::new();
        let block1_hash = block1.header.hash();
        let mut parent = block1.header;
        for (height, name, key) in [(2u64, "2b", 9u8), (3, "3b", 10)] {
            let reward_amount = prover::schedule().reward(height).unwrap();
            let mut reward = transaction::Transaction::new();
            reward.add_output(output::Output::new(&wots::keygen(&[key; 32]).1, reward_amount)).unwrap();
            let txs = [reward];
            let unproven = chain.build_block(&txs).unwrap();
            let (target, min_timestamp) = (unproven.target, unproven.min_timestamp);
            let s = std::time::Instant::now();
            let proof = prover::prove_block(&unproven.inputs, &unproven.outputs, &unproven.nonces, &txs, &unproven.plan, [20 + height as u8; 32]).unwrap();
            timed(&format!("block{name}_proof"), s);
            let mut block = unproven.finish_with_chain_proof(proof, chain_proof);
            block.header.timestamp = block.header.timestamp.max(min_timestamp);
            let s = std::time::Instant::now();
            while !mine_block(&mut block, &target, MINE_BATCH, &difficulty_config().pow) {
                block.header.timestamp = now_millis();
            }
            timed(&format!("block{name}_mining"), s);
            let parent_state = (parent.state_root, parent.output_count);
            assert!(block.validate(&target, &difficulty_config().pow, parent_state, reward_amount));
            let node = prover::block_root(&block.body.proof, &block.body.inputs, &block.body.outputs, &block.body.nonces, &block.state_change(parent_state), height as u32).unwrap();
            info += &format!(
                "BLOCK {name} target {} reward {reward_amount} inputs {} outputs {} challenge {} product {} len {} proof_len {} chain_proof_len {}\n",
                h(&target), block.body.inputs.len(), block.body.outputs.len(), j(&node.challenge), j(&node.product.0),
                block.to_bytes().len(), block.body.proof.as_bytes().len(), block.body.chain_proof.len()
            );
            let hash = block.header.hash();
            chain.apply_block(&block).unwrap();
            let s = std::time::Instant::now();
            chain_proof = chain_prover.prove(&chain.chain_proof_inputs(hash).unwrap(), || chain.chain_proof_inputs(block1_hash).ok(), [30 + height as u8; 32]).unwrap();
            timed(&format!("block{name}_chain_proof"), s);
            info += &tip_line(name, &chain.chain_proof_inputs(hash).unwrap().tip);
            std::fs::write(format!("{out}/block{name}.bin"), block.to_bytes()).unwrap();
            parent = block.header;
        }
        std::fs::write(format!("{out}/chain3b.bin"), &chain_proof).unwrap();
        timed("total", start);
        std::fs::write(format!("{out}/fork.txt"), format!("NETWORK {net}\n{info}{times}")).unwrap();
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn u256_to_f64_matches_small_values_exactly() {
        let mut value = [0u8; 32];
        value[30] = 1;
        value[31] = 2;
        assert_eq!(u256_to_f64(value), 258.0);
        assert_eq!(u256_to_f64([0u8; 32]), 0.0);
    }

    #[test]
    fn hash_rates_pick_a_readable_unit() {
        assert_eq!(format_hash_rate(950.0), "950.0 H/s");
        assert_eq!(format_hash_rate(812_345.0), "812.3 kH/s");
        assert_eq!(format_hash_rate(2_500_000.0), "2.5 MH/s");
    }

    #[test]
    fn durations_pick_a_readable_unit() {
        assert_eq!(format_duration(2.64), "2.6 s");
        assert_eq!(format_duration(252.0), "4.2 min");
        assert_eq!(format_duration(9000.0), "2.5 h");
    }

    #[test]
    fn epoch_is_new_years_day_1970() {
        assert_eq!(format_timestamp(0), "1970-01-01 00:00:00.000 UTC");
    }

    #[test]
    fn one_day_later_rolls_the_date_over() {
        assert_eq!(format_timestamp(86_400_000), "1970-01-02 00:00:00.000 UTC");
    }

    #[test]
    fn time_of_day_decomposes_into_hours_minutes_seconds() {
        // 1h, 1m, 1s past midnight -- same day as the epoch.
        assert_eq!(format_timestamp(3_661_000), "1970-01-01 01:01:01.000 UTC");
    }

    #[test]
    fn milliseconds_decompose_too() {
        assert_eq!(format_timestamp(1_234), "1970-01-01 00:00:01.234 UTC");
    }

    #[test]
    fn a_widely_cited_reference_timestamp_matches() {
        // 1_700_000_000 (seconds) is a commonly-referenced round value,
        // widely cited (independently of this code) as this exact
        // moment -- scaled up to milliseconds, `format_timestamp`'s
        // actual unit now.
        assert_eq!(format_timestamp(1_700_000_000_000), "2023-11-14 22:13:20.000 UTC");
    }
}

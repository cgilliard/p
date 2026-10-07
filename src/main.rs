mod aggregate;
mod block;
mod block_air;
mod bus;
mod chain;
mod chain_rules;
mod chain_step;
mod circuit;
mod cli;
mod discovery;
mod e2e;
mod ext;
mod field;
mod fri;
mod keychain;
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
/// calibration: `Chain`'s retargeting corrects for however wrong it
/// actually is after the first `RETARGET_INTERVAL` blocks regardless,
/// and this number is independent of `block::INITIAL_MAX_HASH` (which
/// stays fixed and easy, since tests built around it need to mine
/// quickly -- see that constant's docs).
const INITIAL_LEADING_ZERO_BITS: u32 = 23;
/// The dev network's (`network`): easier, so proof of work adds little to
/// the proving time that already bounds a block.
const DEV_INITIAL_LEADING_ZERO_BITS: u32 = 20;

/// Retargeting knobs for this driver's actual run -- independent of
/// `chain::DifficultyConfig::for_tests`'s own numbers (see that
/// method's docs for why they're deliberately never the same values).
/// `target_block_time_ms` here is `10_000` (10 real seconds), not the
/// test suite's `10` (milliseconds) -- same window size, genuinely
/// different real-world pace, which is exactly the point of the two
/// being independent numbers.
const RETARGET_INTERVAL: u64 = 10;
const TARGET_BLOCK_TIME_MS: u64 = 60_000;
/// The dev network's. Below what proving takes (~80 s a block on dev), so
/// retargeting eases proof of work as far as it goes and blocks come as
/// fast as they're proven.
const DEV_TARGET_BLOCK_TIME_MS: u64 = 10_000;

/// This network's starting difficulty and block time. Consensus: the
/// chain-proof circuit proves retargeting with these, so changing either
/// means regenerating the network's chain-proof keys (`chain_keys` test)
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
const MAX_ADJUSTMENT_FACTOR: u64 = 4;

/// How many blocks a reorg is ever allowed to unwind in this driver's
/// actual run -- independent of the test suite's own (much smaller)
/// number, same reasoning as the retargeting knobs above. 1000 is a
/// starting point, not a calibration.
const MAX_REORG_DEPTH: u64 = 1000;

/// UDP port discovery listens on when `--port` isn't given.
const DEFAULT_PORT: u16 = 7701;

/// Peer discovery knobs for this driver's actual run (see `discovery`
/// and `peers` for what each one does). Starting points, not
/// calibrations.
const SHARE_LIMIT: u16 = 100;
const MAX_KNOWN_HOSTS: usize = 1000;
const MAX_HOST_FAILURES: u8 = 3;
const PROBE_INTERVAL_MS: u64 = 60_000;
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
        interval: RETARGET_INTERVAL,
        target_block_time_ms: target_block_time_ms(),
        max_adjustment_factor: MAX_ADJUSTMENT_FACTOR,
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
const GENESIS_STATE_ROOT: &str = "5be6bc002e4d0a70dcdf897284a01d5577381315464b6506f65ce56f7d5bc035";
const GENESIS_BODY_HASH: &str = "ab928c73b05ea858df784d11d3ff2f21f3048d5a0c8e6b4714c6f52e56fd8871";

/// A network's genesis: timestamp, nonce, and the resulting hash.
struct Genesis {
    timestamp_ms: u64,
    nonce: &'static str,
    hash: &'static str,
}

const MAIN_GENESIS: Genesis = Genesis {
    timestamp_ms: 1_791_344_142_098,
    nonce: "a23f000000000000000000000000000000000000000000000000000000000000",
    hash: "b10e4411c5b6662e4b14ef3156cbaa43ead98b0db7146f0a9b358659d2e92e4f",
};

const DEV_GENESIS: Genesis = Genesis {
    timestamp_ms: 1_791_344_475_356,
    nonce: "8f13000000000000000000000000000000000000000000000000000000000000",
    hash: "d334f3477d36581ce3083a5cf8758f22712e4b28e517c75a0267f41293b1034f",
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
}

/// Fast sync's default `--sync-depth`: blocks replayed in full after the
/// sync point, and how deep a fast-synced node can reorg at first.
const DEFAULT_SYNC_DEPTH: u64 = 100;

const USAGE: &str = "usage: p [--data-dir PATH] [--port PORT] [--seed IPV4:PORT]... [--no-mine]
         [--log-file PATH] [--log-level trace|debug|info|warn|error] [--log-stdout]
         [--wallet-dir PATH] [--recover] [--passphrase] [--network main|dev]
         [--full-sync] [--sync-depth BLOCKS]";

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

fn spawn_network(storage: &Storage, port: u16, seeds: Vec<SocketAddrV4>) -> Network {
    let socket = std::net::UdpSocket::bind(("0.0.0.0", port)).unwrap_or_else(|e| {
        die(&format!("failed to bind UDP port {port}: {e}"));
    });
    socket
        .set_read_timeout(Some(std::time::Duration::from_millis(SOCKET_READ_TIMEOUT_MS)))
        .expect("failed to set socket read timeout");
    let table = PeerTable::open(storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");
    let discovery = Discovery::new(
        discovery::Config {
            seeds,
            share_limit: SHARE_LIMIT,
            probe_interval_ms: PROBE_INTERVAL_MS,
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
        info!("Listening on UDP port {} (no seeds given).", args.port);
    } else {
        let seeds: Vec<String> = args.seeds.iter().map(|s| s.to_string()).collect();
        info!("Listening on UDP port {}, seeds: {}.", args.port, seeds.join(", "));
    }
    let standalone = args.seeds.is_empty();
    let (received, received_txs, sync_events, commands, peer_height) = spawn_network(&storage, args.port, args.seeds);
    let fast_sync = (fresh && !args.full_sync).then(|| fastsync::FastSync::new(args.sync_depth, &commands));
    let reader = BlockReader::open(&storage).expect("failed to open block reader");
    let peer_table = PeerTable::open(&storage, MAX_KNOWN_HOSTS, MAX_HOST_FAILURES).expect("failed to open peer table");
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

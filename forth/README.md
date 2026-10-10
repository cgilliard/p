# Non-mining node (Forth)

A validating node with no miner, written in Forth so it can be
bootstrapped from a minimal system. The mining node is in `../rust`; the
protocol is described in `../docs`.

## Measurements

Under QEMU (`qemu-system-riscv32`, strict RV32I) on the development laptop,
checking the saved main-network chain (`tests/fixtures/main`, made by the
Rust node's `forth_fixtures` test; 2026-10-08). Block 2 has one input and
three outputs; its proofs are each about 166 KB.

| Check of main block 2 (Forth, QEMU) | Time |
| --- | --- |
| Body hash (hashes both proofs, about 330 KB) | 5.77 s |
| Block proof | 4.40 s |
| Chain proof it carries | 4.40 s |
| Proof of work (64 lookups, about 8,640 permutations) | 6.74 s |
| **All of the above** | **21.4 s** |
| `tipnext`: all of the above plus the header rules and the new tip | 21–27 s |

Timings vary by about a quarter between runs with the laptop's load (QEMU
emulates on one host thread).

The Rust node, natively on the same laptop (12 threads), making that chain:

| | Block 1 | Block 2 |
| --- | --- | --- |
| Block proof | 378.1 s | 311.7 s |
| Mining | 418.5 s | 29.4 s |
| Chain proof | 205.0 s | 194.9 s |
| Validation (`Block::validate`) | under 0.1 s | under 0.1 s |

The genesis chain proof, deriving the chain keys, took 183.5 s.

Primitives (Forth, QEMU): a Poseidon2 permutation about 0.75–0.9 ms, a
field multiply about 0.26 µs. Nearly all of the time above is permutations,
so a faster permutation speeds every check.

`tipnext` checks a block on its parent's tip and computes its own: the tips
it computes for the saved chain match the Rust node's byte for byte. The
two-hour future-drift rule reads QEMU's Goldfish RTC (`hnow`); real hardware
will need its own clock there.

`src/store.fam` keeps every validated block's header and tip in an
append-only log on the virtio disk (one sector each), indexed in memory by
hash, and chooses the best tip by cumulative work. A validating node keeps no
blocks, state or undo data -- a block is checked against its parent's tip
alone -- so a reorganization only moves the best tip. `scripts/test_main.sh`
reruns the main tests and these timings.

`src/state.fam` keeps the chain's state -- the unspent outputs, the index
from commitment to position, and the Merkle tree over them -- on B+trees
(`src/btree.fam`) over a page cache with atomic, journaled commits of any
size (`src/pager.fam`). `src/accept.fam` takes a block: validates it on its
parent's tip, keeps its tip and its state delta, and keeps the state at the
best tip, undoing and reapplying blocks through reorganizations (deltas and
undo data are kept for 1,000 blocks). `src/snap.fam` is fast sync's state, as
the Rust node does it: start at a recent block whose chain proof checks out,
taking the state as of it in pieces each checked against its root on
arrival -- and serve those pieces, as of any recent block, to others.
`src/net.fam` is UDP over virtio-net (ARP, IPv4, polled), and `src/peer.fam`
the Rust node's network protocol over it: discovery with cookies, catching
up block by block (following a peer onto another branch), fast sync, and
serving sync points and state pieces. `scripts/test_net.sh` runs it against
a real Rust node on the host: the Forth node syncs block by block,
reorganizes onto the Rust node's branch, and fast-syncs from it. Accepting main block 3b -- validating
it and reorganizing from block 2 to the 2b/3b branch -- took 21.5 s.

It propagates blocks as the Rust node does, short of mining them: every
block it validates is kept whole (`src/blocks.fam`, on the pager, with the
active chain by height), served (`GET_INV` by hash or height, `GET_CHUNKS`
with the asker's cookie), and a new best block is announced (`INV`) to every
peer but the one it came from; an announced next block is fetched at once.
Its `HOSTS` answers share the peers that have answered it (not 10.0.2.2,
QEMU's view of this machine). A node that asks itself -- a seed list holding
it, a NAT looping back -- knows by the nonce (a `GET_HOSTS` carrying one of
its own), and drops that address for good, as the Rust node does. Hosts
that stop answering aren't dropped -- by either node -- but kept and asked
again every probe interval (a minute), however long they've been silent;
they're not counted, shared or announced to until they answer. A full
table (256 hosts; Forth `peers=N` / `PEERS`, Rust `--max-hosts`) makes room
by evicting the host silent longest among those not answering, never a
seed. The Forth node keeps its table on the disk (32 sectors at the end of
the boot image's 32 MiB), as the Rust node keeps its in LMDB, so after a
restart both sides find each other again without their seeds. So Forth nodes alone can sync each other and
fast-sync new ones. Blocks are kept from where a node started -- a
fast-synced node's sync point, or, on a disk from before this, its next
block -- and nothing is pruned. Run against a mining Rust dev node: a Forth
node synced from it, a second Forth node, knowing only the first, synced
blocks 0--3 from it alone, and blocks mined after reached both.

`src/wallet.fam` is the wallet's seed and keys, as the Rust node makes them
(`../rust/src/wallet.rs`, `mnemonic.rs`, `keychain.rs`): the same 24 BIP39
backup words (`src/bip39.fam`), and passphrase (PBKDF2-HMAC-SHA256,
`src/sha.fam`), give the same keys in either node -- `tests/wallet.fam`
checks them against `forth_wallet_vectors`. It lives in the pager's meta
page, on the node's one disk; starting the chain over keeps it. A new
wallet's seed comes from a virtio entropy device (`src/rng.fam`; `tools/q32`
attaches one). The first run makes a wallet and shows its words once;
`scripts/node.sh --recover` restores one on a new disk, the words typed on
the console (`--passphrase` for a passphrase) -- never passed as settings.
A restored wallet finds its outputs once the node has caught up, by their
recovery nonces in the state, as the Rust node's restore does.

`src/wapi.fam` is the wallet's API: UDP on its own port (the node's + 1,
3738), forwarded from 127.0.0.1 only, every datagram both ways carrying an
HMAC-SHA256 under the wallet's API key, with sessions and counters so
nothing can be replayed. `tools/wallet` (Python, no dependencies) is its
client: `tools/wallet status | balance | outputs`. It asks for the API key
once -- the node shows it when the wallet is made, and
`scripts/node.sh --api-key` reads it from `data/disk.img` (the node may be
running) -- and keeps it in `data/wallet.key`.

Payments are slates, as in the Rust wallet and in the same armored files, so
either can pay the other: `tools/wallet send AMOUNT [FEE]` writes S1,
`receive FILE` answers one with S2, `finalize FILE` signs and submits,
`cancel ID` undoes an unsigned one, `slates` lists them (`src/slate.fam`).
A signed transaction is kept before its signature leaves the node, and
`src/txrelay.fam` announces it to the node's peers until it's confirmed,
serving it as the Rust node's relay does. Both directions have been run
against a Rust dev node, end to end.

`src/image.fam` is the node's boot image. Tabernacle boots the node from
the disk's first 32 MiB when that copy has the hash tabernacle was built
with, and otherwise fetches it from the network. Either way, the node
rebuilds its image from memory (the code, the zeros that are its variables
now, the text), writes it to the disk wherever the disk's copy differs --
so the next boot is from the disk -- and serves it on its own port:
`GET_BIN` (type 15: cookie, hash, first chunk, count) is answered with
`BIN_CHUNK`s (16: hash, index, 1,024 bytes), only with the asker's cookie
and only for its own hash. Tabernacle (`src/tabernacle.S`, assembled into
`src/tabernacle.fam0` by `tools/s2fam0_tabernacle.py`) fetches it the same
way, on the node's port: it asks its seeds for hosts (`GET_HOSTS`), asks
those hosts in turn (up to 32 peers, each answer carrying a cookie). A
`HOSTS` answer may end with a trailer about the answering host: whether it
serves its boot image, and that image's hash (the first 8 bytes) -- a Forth
node and `tools/server.py` send it; the Rust node accepts and ignores it.
After 2 seconds of discovery, tabernacle picks up to 16 of the hosts with
*this* build at random and asks only them for the image, in windows of 32
chunks (a pick that sends nothing after 8 asks is replaced by another);
the seeds only if no other peer has sent any within 5 seconds, so a new
node costs its seeds a few small packets. Nodes hand out their hosts in a
random order, so new nodes spread across the network. A hash mismatch drops
every peer that sent chunks and starts over. `scripts/node.sh` gives
it the seeds as `BOOT` (default: `SEED`); `scripts/makenode.sh` writes a
new build to `data/disk.img` by hand. Under QEMU, with a Rust dev node as
the only seed and one Forth node holding the build, a new node on a blank
disk booted in about 18 s, every chunk from the Forth node.

The compiler's output uses no `jalr` -- every jump is a `jal`, reaching
1 MiB either way -- and returns go through a search tree from return-id to
return site. A program of any size compiles: every 512 KiB or so (at a `:`),
the compiler emits an island, holding the return tree for the segment of
code before it, linked to the islands on either side, and a relay jump for
every word defined so far, which far calls go through (`src/fam.S`,
`emit_island`). A program can have 262,136 call sites; the node has about
8,000.

## Test fixtures

`tests/fixtures/<network>/` holds a real chain from the Rust node: blocks 0
(genesis) to 2 and block 2's chain proof, with `info.txt` (each tip,
target, reward, and the root proofs' challenges and products); and a side
branch on block 1 -- blocks 2b and 3b, outweighing block 2 -- with 3b's chain
proof and `fork.txt`. Regenerate them after any consensus change (about 30
and 20 minutes on main):

    cd ../rust && cargo test --release -- --ignored --nocapture forth_fixtures
    cd ../rust && cargo test --release -- --ignored --nocapture forth_fork_fixtures
    cd ../rust && cargo test --release -- --ignored --nocapture forth_snapshot_fixtures

The last (quick) writes `snap1.bin` and `snap2.bin`: the state as of blocks 1
and 2 as the Rust node serves it -- its sync points and pieces. The wallet's
key vectors (in `tests/wallet.fam`) come from
`cargo test --release -- --ignored --nocapture forth_wallet_vectors`.

Tests load the blocks into memory as a pack (`tools/fxpack`, `tools/fam
--load`, `tests/fx.fam`) rather than compiling them in; `tools/fxinfo` turns
`info.txt` into Forth words.

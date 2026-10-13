# Relays: payment routing and onion routing (design)

Status: design, agreed in discussion 2026-10-12. Built: what "Today"
describes (`forth/src/relay.fam`, `forth/src/pay.fam`), which is the
fallback mode below; phase 0 (the rename); and phase 1 (the list, home
relays: `forth/src/consensus.fam`, `auxtree.fam`, `rlist.fam`;
`rust/src/auxtree.rs`); phase 2 (sender circuits: `forth/src/onion.fam`);
phase 3 (receiver circuits, the same file); and phase 4 (hardening).

## Goals

- Pay a payment address from wallet to wallet, online, with no third
  party able to read the payment and -- once onion routing is in -- none
  able to tell who is paying whom from IP addresses.
- Scale: no fixed set of servers that every wallet talks to.
- Discovery: a node learns the relays from the chain, not by word of mouth.
- Work from day one, when no relays are listed yet (and on test
  networks, which may never list any).
- Never be the only way to pay: a censored user loses convenience, never
  the ability to pay.

## Today (becomes the fallback: seed relays)

What `src/relay.fam` and `src/pay.fam` do now (called gateways until
phase 0):

- A wallet's relays are those set with `userelay=` (up to 4), else the seeds
  (`tabernacle1.root.sx`, `tabernacle2.root.sx`, found by DNS).
- A wallet registers its signed record (its Kyber and Dilithium keys; good
  for 6 hours, made anew hourly) with **every** relay, and sends each a
  KEEP every 20 s so its NAT keeps the way open for deliveries.
- A sender looks the receiver's address up at every relay (the first good
  record wins) and sends every part of every message (PAY1, PAY2) to
  **every** relay; each relay that holds the receiver's record delivers it
  to the IP and port it last heard the receiver from.
- Relays see who talks to whom and when (not what: the payment is end to
  end encrypted), and a lookup's answer carries the receiver's IP.

Every wallet loads every relay equally, so adding relays adds no capacity,
and both parties must share a relay.

## The design in brief

- **One kind of relay.** A relay is a node with a public internet
  connection that the relay list includes. Any relay can serve in any
  position: first hop, middle hop, or an address's home relay. There are
  no exits (nothing leaves the network), so none of Tor's other kinds are
  needed. Nodes behind NAT are clients only.
- **The list is decided by miners**: each block can back a relay list --
  a `consensus.txt` -- as the left branch of the tree under the header's
  `aux_hash`, and the file backed most often over the last day wins -- an
  auxiliary consensus, outside block validity. Like Tor's directory authorities, except that a seat comes
  from hash power.
- **Each address has 3 home relays**, found by hashing the address with
  each relay's id and the epoch: where the receiver registers, where a
  sender looks it up, and where the two meet.
- **Onion routing:** circuits of 2 hops on each side of the home relay:
  `sender → guard → random → HOME ← random ← guard ← receiver`.
- **Until the first list exists** -- the young network, and test networks
  -- nodes use the seeds as relays exactly as today. Which mode applies
  follows from the chain alone, so every node in sync agrees.

## The relay list

### The aux tree

`aux_hash` (any 32 bytes the miner chooses; covered by proof of work and
by the chain proof) is the root of a binary tree, built with SHA-256
(which both nodes already have):

- an internal node is `SHA-256(0x01 ‖ left ‖ right)`; a leaf is
  `SHA-256(0x00 ‖ its bytes)` -- the prefix tells them apart, so a 64-byte
  file can never pass for an internal node;
- the root's **left** child is reserved: the leaf of the `consensus.txt`
  the miner backs, or zeros to abstain;
- the root's **right** child is the miner's own: the root of whatever else
  it commits to -- timestamping, future aux-consensus items, anything.
  Miners with entirely different right sides still count together when
  their left sides match.

An `aux_hash` of all zeros (every block today), a root whose children no
one can fetch, or a left child that isn't a valid `consensus.txt` is an
abstention.

Nothing is added to blocks: the tree travels in its own exchange (below).

### The aux exchange

A content-addressed exchange between peers, separate from blocks:

- `GET_AUX (hash)` asks for the bytes behind a hash; `AUX (hash, bytes)`
  answers -- 64 bytes for an internal node (`left ‖ right`), a leaf's
  bytes for a leaf, in chunks for a large one (as boot-image chunks
  travel). Whatever comes is checked by hashing it, so it can come from
  anyone.
- A node that sees a non-zero `aux_hash` fetches the root's two children,
  then follows the branches it cares about: today the left, and that
  `consensus.txt` if it's new to it. The right side is fetched only by
  whoever wants it.
- Whatever a node has fetched, it serves: the data spreads as blocks do.
  It keeps the roots' children for at least the current and previous
  windows, and the `consensus.txt` files in use.
- Every node does this by default, with a setting to turn it off. Peers
  that don't know the messages (the Rust node, until it does) ignore them.

A miner who never publishes its tree simply isn't counted. Nodes
disagreeing over a withheld vote would mean the network is under attack,
and then the file-based ways to pay (below) are what to rely on.

### consensus.txt

The relay list: one entry for each relay, each signed by the relay
itself --

| Field | |
|---|---|
| magic, version | `"RLY1"` |
| network | 0 main, 1 dev |
| expiry | when the entry stops being good |
| Dilithium public key | its identity; its **relay id** = SHA3-256 of it |
| Kyber public key | its onion key (circuits) |
| IP, port | where it's reached |
| signature | the relay's (Dilithium), over all of the above |

-- about 4.6 KB an entry, sorted by relay id. The relay's own signature
means no one can list someone else's address (and point the network's
traffic at a victim), and wallets can authenticate each relay. The file
holds everything a node needs: there's nothing else to fetch. A relay
that moves needs a new entry, in the next version of the file; a new
entry also brings a new onion key (phase 4).

**The file with the most votes in the window wins, however few they
are.**

### Tallying (proposed parameters)

| | |
|---|---|
| Epoch | 144 blocks (a day) |
| Window | the 144 blocks ending 12 blocks (about 2 hours) before the epoch starts |
| The list | the `consensus.txt` backed by the most blocks in the window, however few (1% wins if it's the most); a tie goes to the file whose latest vote is newest |
| Enough relays | the file lists at least 8 with entries not expired (a path needs 5 distinct ones) |

For example, epoch 10 is heights 1,440–1,583; its window is heights
1,284–1,427. The 12-block margin means the window's newest block has 12
confirmations when the epoch begins (a reorg won't change the list in
use), and gives everyone about 2 hours to fetch the winning file, and
wallets to register with their new home relays, before the switch.

Everything is decided by one window, so a node knows exactly how far back
it must see: at most 300 blocks (143 into the epoch, the 12-block margin,
the window of 144, and the block below it: the last epoch's seed), never an unknown stretch of history. It needs only
their **headers** (`aux_hash` is in each): about 55 KB, fetched from
peers and checked by hash, each naming the one before, back from the
node's tip -- a header backfill, independent of how deep the node
fast-synced (its full blocks start at the sync point, 25 back by
default). The list for an epoch is fixed before the epoch begins, so
every node agrees on it at every height. A node also needs each
window block's root children (64 bytes each) and the winning file, from
the aux exchange.

**Abstaining is free.** A block that backs no file simply isn't counted:
a miner sitting out changes nothing. The node shows how much stands behind
the list in use -- "relay list: 37 of the last 144 blocks voted, 35 for
this list, 2 unresolved" (unresolved: blocks whose tree it couldn't
fetch) -- so users can judge it.

## Fallback: seed relays until the first list

Which mode applies at a height follows **from the chain** (and the aux
data behind it, which honest miners publish) -- never from how far a node
has got fetching -- so every node in sync agrees, and a sender and a
receiver always look for each other in the same place:

- **Listed mode** for an epoch whose window has at least one vote, and
  whose winning file lists at least 8 relays.
- **Seed mode** (today's model) otherwise: the young network, test
  networks, and any later epoch in whose window not one block votes.
  The relays are the seeds (by DNS) or `userelay=`; every relay holds every
  record; no circuits.

The mode depends on the window alone, like the list: a rule
such as "once listed, never back to the seeds" would need to know whether
a list ever existed, an unbounded look back.

A node that hasn't yet fetched what it needs to know the list (the
window's headers, the roots' children, the winning file) doesn't fall back: its
payments wait until it has them (the wallet's status says so) -- falling
back on its own, it would look where no one else is.

A switch of mode happens at an epoch boundary, and nodes in sync make it
at the same height. Home relays move at every boundary (the epoch seed),
so for the first quarter of each epoch (36 blocks, about 6 hours; dev 3)
a wallet registers with both its old and its new home relays -- the old
by the last epoch's seed -- and a lookup or a message goes to both.

Two settings override the chain, and work only between nodes that both
use them:

- `userelay=`: exactly these relays, seed-mode style -- two people can agree
  on a private relay outside the list.
- `seedmode`: seed mode whatever the chain says, for testing (on a
  private or test network that lists no relays, it's the mode anyway).

## Home relays

An address's home relays for an epoch are the 3 listed relays with the
highest `SHA3-256("tabernacle-home-v1" ‖ address ‖ relay id ‖ epoch
seed)`, the epoch seed being the id of the window's last block
(rendezvous hashing). The last epoch's seed is then the id of the block
just below the window, so a node needs the window's headers and one more.

- When the list changes, only addresses whose top 3 changed move.
- The epoch seed moves every address each epoch, and isn't known until
  12 blocks (about 2 hours) before the epoch starts, so no one can set
  relays up in advance to become a particular address's home.
- The receiver registers with all 3 and keeps a circuit to each; a sender
  uses whichever answers first, so one down or hostile home relay can't
  block payments.
- Each relay holds only its share of the addresses: about 3/N of the
  network, not all of it.

## Circuits (onion routing)

```
sender → guard → middle → HOME ← middle ← guard ← receiver
```

- **Guard:** each wallet keeps the same first relay for months. With a
  fresh first hop every time, an attacker running some relays would sooner
  or later be first hop of one of your circuits and see your IP; with a
  guard you're either unlucky once or safe for long. It's also the only
  relay a receiver keeps its NAT open to.
- **Middle:** random, per circuit. The receiver's circuits are rebuilt as
  it re-registers (hourly); a sender's, per payment.
- **Home:** the address's home relay. It holds the record and joins the
  sender's circuit to the receiver's. Lookup and payment go through one
  circuit: the sender asks for the record, then sends PAY1 on the same
  circuit. (In Tor the directory, the introduction point and the
  rendezvous point are different relays; here one relay does all three --
  payments are a few KB, so carrying them is cheap, and it saves round
  trips. The home relay knows which address it serves, since that's
  computed from the address; it never learns either side's IP.)
- **Path rules:** five distinct relays; no two in one /16 (a cheap guess at
  "one operator"); never your own home relay as one of your hops. When
  your guard is one of your home relays for an epoch, the next-best guard
  by the same score stands in, so a wallet's guards stay a small fixed set.

**Circuits, not self-contained onion packets.** A Sphinx-style packet
(Lightning, Nym) carries its whole route in every packet, which needs
key blinding -- elliptic curves only, nothing post-quantum. With Kyber
each hop would cost a 768-byte ciphertext in every packet, more than a
datagram holds for 3 hops. A circuit is set up once, a Kyber handshake
with each relay in turn, and then every cell is symmetric (ChaCha20-
Poly1305, a layer per hop).

**The handshake** follows PAY1/PAY2: the client encapsulates a key to the
relay's onion key (Kyber) and sends a one-time Kyber key; the relay
encapsulates a second key to the one-time key; the circuit's keys come
from both and the transcript (SHAKE256). The one-time key is thrown away,
so the circuit is forward secret even if the onion key later leaks.

**Cells** are fixed size, so their size tells an observer nothing. The
handshake (a 768-byte ciphertext and an 800-byte key) is larger than one
datagram's worth, so it spans two cells.

## Phases

Each phase works on its own; the fallbacks stay throughout.

0. **Rename** gateways to relays in the code and settings (keeping
   `usegw=` and `gateway` as aliases; the wire format unchanged). This is
   seed mode, which stays as the young network's and test networks'
   mode. *Done 2026-10-12.*
1. **The list:** the aux tree and exchange, `consensus.txt`, tallying, the mode
   switch, home relays. Relays relay as today (no circuits), but each
   address uses only its 3 home relays: discovery and load solved; relays
   still see IPs. *Done 2026-10-13.*
2. **Sender circuits:** the sender reaches the home relay through guard
   and middle. Its IP is hidden from the home relay and the receiver.
   *Done 2026-10-13.*
3. **Receiver circuits:** the receiver registers and is reached through its
   circuits; records stop carrying an IP. Its IP is hidden too. *Done
   2026-10-13.*
4. **Hardening:** guards' lifetimes and rotation, onion-key rotation,
   padding, and (payments tolerate delay) optional mixing delays.
   *Done 2026-10-13.*

## Implementation plan: phase 1 (done 2026-10-13)

Tried live on a private dev chain: a Rust miner backing a consensus.txt
of 3 Forth relays, and 2 Forth wallets. All five Forth nodes went to
listed mode within 3 seconds of each other when epoch 1 began (6 of its
window's 10 blocks voted, all for the file), each having fetched the
miner's tree and file and checked the relays' signatures; the wallets
registered with their home relays; one looked the other up (1.4 s) and
paid it by address (3.2 s), mined. Epoch 2: 12 of 12 voted.

Decided for phase 1 (changeable):

- **A relay's keys** come from its wallet's seed, as the payment address's
  do, under their own tags: Dilithium's ξ = SHAKE256("tabernacle-relay-
  dilithium-v1" ‖ seed ‖ 0, 32), and its relay id is SHA3-256 of the
  Dilithium key. The onion key: Kyber's (d, z) = SHAKE256("tabernacle-
  relay-kyber-v1" ‖ seed ‖ g, 64), g the entry's expiry's low 32 bits
  (phase 4; 0 before).
- **An entry** (0x11CC bytes, laid out like a wallet's record): 0 "RLY1"
  4 the network (u32) 8 IP (4) 0C port (2) 0E zeros (2) 10 expiry (ms
  since the epoch, u64) 18 Kyber's key (0x320) 338 Dilithium's (0x520)
  858 the signature (Dilithium, over bytes 0 .. 858). Numbers big-endian.
- **`consensus.txt`** is text: a first line `tabernacle-consensus 1 main`
  (or `dev`), then one line `relay <the entry, in hex>` per relay, sorted
  by relay id, each line ending in a newline. A file that breaks any rule
  -- a bad line, a bad signature, another network, unsorted -- is not
  valid, and backs nothing. Expired entries are skipped, not fatal.
- **The aux tree's bytes:** a node's bytes are `0x01 ‖ left ‖ right` (65)
  and a leaf's `0x00 ‖ its content`; every hash is SHA-256 of those bytes,
  so the aux exchange is purely "the bytes whose SHA-256 is this".
- **New messages** (types the Rust node doesn't know are ignored by it):
  - `0x17 GET_AUX`: cookie (8), hash (32), first chunk (u32), count (u16)
  - `0x18 AUX`: hash (32), total length (u32), chunk (u32), up to 0x400 bytes
  - `0x19 GET_HDRS`: cookie (8), first height (u32), count (u16, up to 6:
    a datagram holds at most 1,200 bytes)
  - `0x1A HDRS`: first height (u32), count (u16), that many 188-byte headers
- **Dev parameters**, so a test needs minutes, not days: an epoch of 12
  blocks, a margin of 2, at least 3 relays. Main: 144, 12, 8.

Steps, each tested before the next:

1. **Entries and the file** (Forth): make and check an entry; read and
   check `consensus.txt`; the aux tree's hashing. The API's `relayentry
   ip port days` and `tools/wallet relay-entry` print a relay's signed
   line; `tools/consensus` assembles lines into a sorted file.
2. **The miner** (Rust): `--consensus-file PATH` sets `aux_hash` to
   `SHA-256(0x01 ‖ leaf ‖ 32 zeros)`; it answers GET_AUX for its tree and
   file, and GET_HDRS from its chain.
3. **The aux exchange** (Forth): fetch, check, keep and serve by hash.
4. **The header backfill** (Forth): the window's headers by GET_HDRS,
   checked by hash back from the tip; served from the node's own blocks
   and what it backfilled.
5. **The tally**: per epoch, the window's votes, the winning file, the
   mode; the status line (and the API's `status`).
6. **Routing**: home relays by rendezvous hashing; registering, looking up
   and relaying through them (and the last epoch's, for a while after a
   boundary) in listed mode; seed mode as today.
7. **A live test**: a private dev chain -- a Rust miner backing a test
   file, 4 Forth relays, two Forth wallets paying each other -- through a
   switch from seed mode to listed mode.

## Implementation plan: phase 2 (sender circuits; done 2026-10-13)

Tried live on a private dev chain (blocks unproven, for speed): 4 Forth
relays, 2 Forth wallets. w1 paid w2 by address in 8.4 s: its circuit --
guard r1, middle r4 -- to r2, w2's home relay, built in 1.7 s, carried
the lookup and PAY1; w2 answered through its own circuit (r1, r4) to r3,
w1's home relay; mined. The relays' logs show what each saw: the guard
the two wallets; the middle the guard; each home relay only the middle.

In listed mode the sender reaches one of the receiver's home relays through
a circuit of three relays -- guard, middle, home -- and the home relay does
the lookup and relays the payment's parts itself, at the end of the
circuit. No relay sees both the sender's address and the receiver's: the
guard knows the sender, the home the receiver, the middle neither. The
receiver is still reached directly (its registration carries its IP until
phase 3).

**Messages** (big-endian; between relays and clients, types the Rust node
ignores):

| Type | Name | Body |
|---|---|---|
| 0x1B | CREATE1 | circuit id (4), ct1 (0x300): a key encapsulated to the relay's onion key |
| 0x1C | CREATE2 | circuit id (4), a one-time Kyber key (0x320) |
| 0x1D | CREATED | circuit id (4), ct2 (0x300), confirmation (16) |
| 0x1E | CELL | circuit id (4), nonce (12), body (0x450): towards the end |
| 0x1F | BCELL | circuit id (4), nonce (12), body (0x450): back to the client |

A circuit id names the circuit on one link (chosen by the side that sent
CREATE). The handshake follows PAY1/PAY2: the relay decapsulates ct1 with
its onion key (k1), encapsulates to the one-time key (ct2, k2); the keys
are SHAKE256("tabernacle-circuit-v1" ‖ k1 ‖ k2 ‖ SHA3-256(ct1 ‖ key ‖
ct2), 0x50): forward 32, backward 32, then the 16 bytes CREATED returns
to show the relay derived them. The one-time key is thrown away: forward
secret.

**Cells.** A cell's body is ChaCha20-Poly1305 under the key of the hop at
the circuit's end (its 0x440 bytes, then the tag), then plain ChaCha20
under each hop before it; each hop strips its layer with the nonce the
cell carries (random, chosen by whoever sends it), and the last checks the
tag. Back, the end seals, each hop adds its layer, the client takes them
off. A relay knows it's the end by having no next hop. Inside: a command
(1), a length (2), the bytes (zeros after):

- `EXTEND1` ip (4), port (2), ct1; `EXTEND2` the one-time key: the end
  extends the circuit to that relay (CREATE1, CREATE2), and answers
  `EXTENDED` ct2, confirmation.
- `ASK` address (32): the end, a home relay, answers `FOUND` -- the record
  and where it was heard from, in parts: part, parts, bytes -- or
  `NOTFOUND`.
- `RELAY` address (32), then a message's part as a RELAY carries it: the end
  delivers it (DELIVER) to where it heard the address from.

**Paths.** The home: one of the receiver's home relays (the next, if a
circuit to it fails). The guard: the live relay with the highest
SHA3-256("tabernacle-guard-v1" ‖ the wallet's seed ‖ the month), so it
stays for a month without being stored. The middle: random. Three
different relays; on main, no two in one /16, and none of our own home
relays, when the list leaves room for that.

**Limits.** A relay keeps at most 64 circuits (idle 10 minutes: dropped),
and starts at most one CREATE from an IP every 2 s (each costs it a
decapsulation and an encapsulation). A circuit failing to build in 5 s is
built anew, at most twice for a home relay, then the next home relay.

**Settings.** `direct`: no circuits (phase 1's routing), for testing.

Steps:

1. The handshake and the layers (Forth), tested with both sides in one
   process.
2. The relay's side: CREATE, CREATED, cells forward and back, EXTEND, and
   at the end ASK and RELAY.
3. The client's side: the path, building, ASK and RELAY through the
   circuit, the answers back; lookups and payments use it in listed mode.
4. A live test: a private dev chain, 4 relays, 2 wallets.

## Implementation plan: phase 3 (receiver circuits; done 2026-10-13)

Tried live on the same private dev chain (4 relays, 2 wallets). Each
wallet built a circuit to each of its 3 home relays (one at a time, about
1--2 s each, all up within a minute of starting) and registered along
them. w1 paid w2 by address in 7.3 s, and w2 paid w1 in 7.6 s, both
mined; no relay sent a DELIVER to a wallet, and a lookup of w2 answered
0.0.0.0:0. Across two epoch changes each wallet built only the circuit
its new home relay needed.

In listed mode the receiver keeps a circuit -- guard, middle, home -- to
each of its home relays (and, for the first quarter of an epoch, the last
epoch's), registers its record along it, and is delivered to back along
it. A home relay then knows an address and a circuit, never the
receiver's IP: only the guard sees that, and the guard doesn't know the
address.

**More cell commands** (inside, as phase 2's):

- `REGISTER` part, parts, bytes: the record, in 5 parts. The end keeps
  it (as a REG) with the circuit as the way back -- in the directory's
  ip and port fields, the circuit's id and 0xFFFF0000 + its slot -- and
  answers `REGISTERED` status (as ACK's), the address. One registration
  a circuit every 10 s.
- `DELIVER` a part as 0x15 carries it: from the end, back along the
  receiver's circuit, when a `RELAY` (by circuit) names an address
  registered that way.
- `KEEP`: nothing; down each circuit for receiving every 4 minutes, so the
  relays don't drop it as idle (10 minutes).

**Records stop carrying an IP:** a lookup (FOUND, or a seed-mode PART)
of an address registered by circuit gives 0.0.0.0:0, and a direct
`RELAY` (0x14) to it isn't delivered: a sender with `direct` can't pay a
receiver using circuits.

**The client** keeps 9 circuits: one for sending (phase 2's), one for
each of up to 8 home relays. One is built at a time, sending first (a
guard starts at most one circuit from an IP every 2 s). A circuit for
receiving that fails is tried again in 30 s; one an hour old is built
anew. A new one means a new record (a new sequence, so the relays take
the new way back -- a record seen before can't redirect deliveries) and
registering it along every circuit. When the home relays change, a
circuit to a relay still among them is kept. For its NAT the wallet
sends its guard a KEEP every 20 s; it no longer talks to its home
relays directly at all (nor, sending, to the receiver's): with circuits
in use they aren't made peers.

**A relay** exempts listed relays from the CREATE limit (a guard extends
many circuits), and keeps 64 circuits -- too few once there are many
wallets, each holding 3: for phase 4.

## Implementation plan: phase 4 (hardening; done 2026-10-13)

Tried live on the same private dev chain, the relays run with
`--mix-delay 300` and with padding on. w1 paid w2 in 10.3 s (7.3 s
without). Then r1 was stopped. About 4 minutes later w1's KEEPs went
unanswered down the circuits through it; each was built anew, and after 3
failed tries through r1 as guard it was passed over. With r1 (one of w1's
home relays) still down, w2 paid w1 in 11.3 s, mined.

- **Capacity.** A relay keeps up to 4096 circuits (was 64): 0x80 bytes
  each, found by two hash chains (by where a circuit comes from and where
  it goes on to) instead of a scan. A handshake's 1.6 KB (ct1 and the
  one-time key, then CREATED's ct2 and confirmation; or an EXTEND's) sits
  in one of 16 shared buffers only while it's under way: freed when the
  first cell comes (the client has CREATED) or the next hop answers, or
  taken over after 30 s.
- **CREATE limits.** Per IP, 4 at once, then one every 2 s (wallets
  behind one carrier-grade NAT get a burst, not one every 2 s); listed
  relays exempt. In all, 10 at once, then one every 100 ms: each costs a
  decapsulation and an encapsulation. (A leaky bucket: GCRA.)
- **Guards.** The period (2^32 ms, about 50 days) is offset per wallet,
  by SHA3-256("tabernacle-guard-offset-v1" ‖ seed), so wallets don't all
  change guard at once. A guard that doesn't answer 3 circuits running is
  passed over for 30 minutes; the next by its score stands in.
- **Knowing a circuit's gone.** The end answers a KEEP. A circuit for
  receiving whose KEEP (every 4 minutes) goes unanswered for 20 s is built
  anew. Sending a message also sends a KEEP, and a sending circuit whose
  KEEP goes unanswered for 10 s, or that's been idle 2 minutes, is built
  anew -- so a dead hop costs one retry of the message, not the payment.
- **Onion keys rotate with entries.** The onion key comes from the seed
  and the entry's expiry, so each new entry (an operator must renew it
  within 30 days) brings a new key. The relay uses the key of its entry in
  the list in use, so no new field or message is needed. Forward secrecy
  doesn't depend on this (the one-time key gives it). Rotation limits how
  long a leaked onion key can be used to impersonate the relay -- though,
  derived from the seed, it doesn't help if the seed itself leaks.
- **Padding.** A message sent by circuit is padded to a power of two of
  parts with parts numbered 0xFF, which travel the whole way (DELIVERed
  like any) and are dropped by the receiver. So the number of cells says
  only the message's size class. Cells were already all one size.
- **Mixing delays** (optional): `mixdelay=MS` (`node.sh --mix-delay MS`,
  at most 10 s) holds each cell a relay passes on, either way, a random
  0 .. MS first (up to 32 held; more go at once). Handshakes aren't
  delayed. With few users there's little to mix with, so it's off by
  default.
- **Settings** for testing are now in `node.sh` too: `--direct`,
  `--seed-mode`.

## Fallbacks for a user

From most convenient to most robust, each relying on less:

1. pay by address through the listed relays (or the seeds, in seed mode);
2. pay by address through relays agreed with the other person (`userelay=`);
3. exchange slate files by any channel (the Slates tab: make, answer,
   finalize) -- only the two nodes involved.

Censoring the relay list stops only automatic routing to an address; the
transaction still goes to the ordinary peer network and is mined like any
other.

## Limits

- An address's home relays can be computed by anyone, so they're the
  obvious target: flooding them can block payments to that address (Tor's
  onion-service directories share this). Mitigated by 3 home relays, the
  epoch moving them, and the fallbacks. A home relay also sees when its
  addresses are paid, but not by whom.
- Low-latency onion routing doesn't stop someone watching both ends of a
  path from matching timing; early on, few users means a small crowd.
  Mixing delays only help once there's a crowd.
- A relay that hasn't fetched the list yet uses an onion key no one
  expects, so circuits through it fail until it has (seen at start-up).
- On-chain privacy is a separate matter.

## Open questions

- The parameters above (epoch, window, margin, 3 home relays,
  minimum list size).
- The new message types (the aux exchange, the circuit cells): settled
  in phases 1--3, open to change before launch.
- How many circuits a relay holds (4096) and the CREATE limits: to tune
  once relays' real load is known.
- How long an entry in `consensus.txt` lives (now up to 30 days), which
  is also how often onion keys rotate; and onion keys made at random and
  kept on the relay's disk, rather than from the seed.
- Whether mixing delays should be on by default once there are enough
  users to mix with.
- Receiving as an opt-in setting (only nodes accepting payments register
  and keep their NAT open), and KEEPs only to a relay nothing else has
  been sent to lately -- in seed mode the node's peer traffic to the
  seeds (heights, host probes, about once a minute) already keeps the
  path open on most routers.
- Whether the Rust node relays, or relays are Forth nodes only.

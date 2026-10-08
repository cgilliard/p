# Chain recursion and fast sync: design proposal

Goal: every block's proof attests the **whole chain** up to it, so a new
node can sync by downloading the tip's header, its proof, and a snapshot
of the current state -- verifying one ~120 KB proof in ~10 ms instead of
replaying every block. Light clients get the same guarantee for free.

This extends `docs/RECURSION.md` (which aggregates one block's
transactions into one proof) one level up: aggregating each block's
proof with its parent's.

## Why: what a full node checks that block proofs don't

Today a full node accepts block N when:

1. **Its header is valid**: links to the parent (`prev_hash`, `height`),
   timestamp strictly after the parent's (and not too far in the node's
   future), proof of work meets the target, and the target follows the
   retarget rule.
2. **Its proof is valid**: the transactions balance against the reward
   and every input is signed by its owner (`prover::Proof::verify`, the
   block statement over the body's commitment lists and nonces).
3. **It applies to the state**: every input is an existing, unspent
   output (resolved through the UTXO index, marked spent in the bitmap),
   no output already exists, and the resulting PMMR and bitmap roots
   are the ones the header claims.

A block proof covers only (2). Part (3) is what rules out spending
outputs that never existed, and double spends -- today it's guaranteed
only by every node replaying every block. **A chain proof must cover
all three**, inductively: if block N-1's proof attests the chain up to
N-1, block N's attests the chain up to N.

With (3) proven, "the unspent set holds exactly the coins ever issued"
follows by induction even though nobody knows the hidden amounts: each
block's statement says its inputs plus the reward equal its outputs, and
(3) says those inputs were real and are now gone.

## The design: in-consensus, one chain step per block

Every block's proof becomes a **chain proof**: its statement includes
everything about the chain before it. Its top level is a *chain step*
circuit -- the same kind of node as `aggregate`'s, verifying child
proofs -- with three children:

```text
            chain step (block N)
           /        |          \
  parent's     block N's       block N's
  chain proof  contents proof  state transition
  (N-1)        (today's tree   (parent's roots ->
               root / wrap)     N's roots)
```

plus header checks for the **parent**, done in the chain step itself.

### What block N's chain proof attests

Its public statement:

- `prev_hash` (the parent's header hash) -- and, through the parent's
  chain proof, everything before it back to genesis;
- block N's state roots (`pmmr_root`, `bitmap_root`) and `height`;
- a digest of block N's body lists (inputs, outputs, nonces);
- the cumulative work (for choosing between forks) and the retarget
  state the next block must follow.

### The circularity, and how it's resolved

Block N's `body_hash` covers block N's proof, and its header covers the
`body_hash` -- so block N's proof **can't attest block N's own header**
(it would have to contain its own hash). So:

- block N's chain proof checks the **parent's** header in full (PoW,
  target, timestamp, link) -- which the parent's proof couldn't;
- a verifier checks the **tip's** header natively: its PoW, its link and
  roots against the proof's statement, its `body_hash` against the body.

One header checked natively, everything else by the proof.

### Genesis

Genesis is fixed and has no parent: block 1's chain step takes genesis's
header and state roots as constants instead of verifying a parent proof.
(Or the chain step has a "base case" flag, as in standard IVC.)

### Uniform proofs

Recursion needs every block's top-level proof to have **one shape**, so
one chain-step circuit can verify any parent. Today a block's proof is
direct (variable size) or a tree root (fixed). Under this design every
block's contents proof is wrapped to the fixed tree shape, and every
chain proof is a chain-step proof: a uniform ~120 KB (plus the chunk
indices), ~10 ms to verify.

## Part (1) in the circuit: header checks

- **Proof of work**: `hash_bytes_32(pow_preimage ‖ nonce) <= target`.
  Poseidon2, so cheap to prove -- a few permutations, plus repacking the
  176 header bytes (see "Byte hashing" below), plus a 256-bit comparison.
  (Bitcoin's SHA-256 would be very expensive here; this is a real
  advantage of Poseidon2 PoW.)
- **Link**: the parent's header hash is the statement's `prev_hash`;
  heights increase by one.
- **Timestamp**: strictly after its own parent's (checked one level
  down: the chain step for N checks N-1's against N-2's, from N-1's
  proof statement). The "not too far in the future" rule depends on the
  local clock and **can't be proven** -- a syncing node can apply it to
  the tip only. That's standard for any proof-based sync, and harmless:
  a far-future timestamp only affects retargeting, which the proof
  checks against the chain's own timestamps.
- **Retarget**: every `RETARGET_INTERVAL` (10) blocks, the target scales
  by the window's actual vs expected time, clamped to
  `MAX_ADJUSTMENT_FACTOR` (4). In the circuit that's 256-bit
  multiply/divide on the target -- awkward but bounded (limb arithmetic,
  like the amount limbs).
- **Cumulative work**: summed per block (256-bit addition), so a syncing
  node can compare competing tips by work, as a full node does.

## Part (3) in the circuit: the state transition

This is the part that's new, and **the main unknown is its cost**.

### Per block

For each input (commitment `c`):
1. **Exists**: `c` is the leaf at some position `p` of the PMMR -- a
   membership path from the leaf to a peak, and the peaks bag to the
   parent's `pmmr_root`.
2. **Unspent, then spent**: bit `p` of the bitmap is 0 under the
   parent's `bitmap_root`, and setting it gives the next root -- a
   membership path in the bitmap's tree, recomputed with the bit set.

For each output: **appended** to the PMMR (merges along the right edge;
amortized ~2 node hashes per leaf) -- and **no duplicate of a live
output**. (Today that's a UTXO-index lookup; in the circuit it needs a
non-membership argument, or a rule that makes duplicates impossible
outright -- see open questions.)

Finally the new peaks bag to N's `pmmr_root`, and the bitmap updates
compose to N's `bitmap_root`.

### What today's structures cost in a circuit

Both commitments were designed for native speed, not for circuits:

- **Byte hashing.** Every node hash is `hash_bytes_32` over bytes --
  `pos ‖ left ‖ right` (72 bytes) for the PMMR, `level ‖ left ‖ right`
  (68 bytes) for the bitmap. `hash_bytes` packs **3 bytes per field
  element**, but a digest is 8 elements of **4 bytes** each; so in the
  circuit every node hash means decomposing two digests into bytes and
  repacking them (range checks on every byte), plus 2 permutations.
- **Bitmap pages.** A leaf is a 4096-byte page (`PAGE_BYTES`), hashed
  as ~1366 elements -- **~86 permutations** to re-hash one page when a
  bit in it changes.
- **Bitmap depth.** `DEPTH` = 49 levels above the pages (sized so every
  `u64` position has a page) -- ~49 node hashes per update, though only
  ~25 levels are ever populated below a billion outputs.
- **Peak bagging.** One `hash_bytes` over all peaks (up to ~30 × 40
  bytes) -- ~25 permutations, but once per block, not per input.

Rough per-input estimate today (**to be measured**): PMMR path ~30 node
hashes + bitmap check-and-set ~2 × (86 + 49 × 2) permutations, plus the
byte repacking -- on the order of **400+ permutations per input**, more
than the ~260 a block proof already spends per input (WOTS chains and
public-key hashing). Proving per block would roughly double or worse.

### A circuit-friendly state (consensus change, cheapest now)

What it could look like -- the spike should measure both:

- **Hash elements, not bytes**: node = `hash_elements(DOMAIN, left(8) ‖
  right(8))` with the level or position in the capacity -- one
  permutation, no repacking.
- **Small bitmap leaves**: a leaf of a few field elements (e.g. 8 × 31
  bits = 248 positions, one digest) instead of a 4 KB page: re-hashing a
  leaf is one permutation.
- **Depth sized to use**: ~32 levels (4 billion leaves × 248 positions)
  rather than 49.

Estimate: ~32 (PMMR path) + ~2 × 33 (bitmap) ≈ **~100 permutations per
input**, no repacking -- under half of what a block proof spends per
input already. Alternatives worth comparing: one combined structure
(each PMMR leaf carries its own spent flag, so a spend is one path
update), or an indexed Merkle tree of unspent commitments (which would
also give non-membership for the duplicate check).

## The cost: a proving floor, on the critical path

- **Floor**: every block, even an empty one, pays one chain step --
  verifying the parent's chain proof and its contents proof, about one
  aggregation step today (~60 s on a laptop CPU, far less on a GPU).
  Today an empty block proves in ~1 s.
- **Critical path**: a miner can't start proof of work on block N+1
  until it has proven N+1, which needs N's proof. After every new block,
  every miner spends one chain step (plus its contents and transition
  proofs) before mining. That's fine at a 10-minute block time; at 1
  minute, slow provers lose races and orphan rates rise. **Block time
  should be decided with measured chain-step times.**
- **Ahead of time**: the contents and transition proofs depend only on
  the mempool and the parent's state, so a miner can prove them while
  the parent is being mined -- only the chain step itself has to wait
  for the parent's proof.

## Fast sync

(Implemented: step 5d below.) Every node syncs this way -- there are no
light clients: a fast-synced node validates everything a replaying node
would, with the chain proof standing in for replaying history.

A new node, holding only the genesis block:

1. **Picks the sync point** H = best peer height − `depth` (default 100,
   `--sync-depth`). No headers are downloaded: the chain proof vouches
   for every header up to H.
2. **Fetches blocks H and H+1.** Block H+1 carries π_H, the chain proof
   of H.
3. **Gets H's sync point** -- the target, retarget anchor (the first
   block's timestamp) and cumulative work after H -- from any peer, and
   believes it once π_H verifies against H's header and it
   (`Chain::check_sync_point`): every block up to H valid, every state
   transition right, proof of work and retargeting followed, that much
   work.
4. **Downloads the state as of H** from every peer at once, piece by
   piece, each checked on arrival (below).
5. **Starts at H** (`Chain::import_snapshot`): the snapshot must hash to
   H's state root with H's output count, with no two unspent outputs
   alike -- which also checks the no-duplicate-output rule as of H.
6. **Applies H+1 … tip in full**, as any node does -- block proofs, chain
   proofs, every native rule. It's then a full node at the tip.

No reorg reaches below H (`reorg_floor`), so `depth` is also how deep a
fast-synced node can reorg at first; that grows as it runs.

**Serving needs no stored snapshot.** A peer serves the state as of any
active block from its reorg floor up: the current tree, with the outputs
each later block spent put back (its undo data says which) and the
outputs appended since cut off (`state_tree::AsOf`), computed when asked
(`chain::StateReader`).

### The snapshot

With the state tree (`state_tree.rs`), **the whole tree follows from
`output_count` and the unspent outputs**: every position below the count
not holding an unspent output is `SPENT`, every position above it is
`EMPTY`, and an all-`SPENT` or all-`EMPTY` subtree has a fixed hash per
height. So a snapshot is only:

- `output_count`, and
- every unspent output's position, commitment, and recovery nonce.

No spent history, no internal hashes, no bitmap: it grows with the
unspent set, not with history. Each leaf is `leaf(commitment, nonce)`, so
the root authenticates the nonces as well as the commitments.

**Parallel and trustless** (`snapshot.rs`, `statesync.rs`): the tree is
fetched as *pieces*, each a subtree whose hash is already known:

1. An inner piece (levels 32, 24, 16) is the hashes 8 levels down (4 for
   the last: up to 256 hashes, 8 KB); they must hash up to the piece's
   own hash, which authenticates them all.
2. A leaf piece (level 12: 4,096 positions) is the subtree's unspent
   outputs, up to ~200 KB; with the output count, they must hash to the
   piece's hash.
3. Pieces download from every peer in parallel (16 at a time). A piece
   that doesn't match identifies the peer that lied: it's banned from
   the sync and the piece fetched elsewhere. A subtree whose hash is the
   all-`SPENT` (or all-`EMPTY`) one needs no download at all, so
   mostly-spent history costs almost nothing.

The state isn't append-only, unlike a PMMR's hashes: spending changes a
leaf anywhere in history, so pieces are fetched *as of H*, not of a
moving tip. (Grin's txhashset is pinned to a horizon header for the same
reason: its leaf-set bitmap changes with every spend.) Fully spent
subtrees never change again, and the imported tree stores them as their
root alone.

The worst a peer can do is withhold (retry elsewhere) or send a bad
chunk (detected and attributed, as with a bad bitmap page).

**Recovery on a fast-synced node**: its state has no spent outputs, so
wallet recovery can't see keys whose outputs were all spent -- which
signed, and must never be handed out again. Such a node's chain view
reports `has_full_history() == false`, and recovery then resumes keys
`RECOVERY_INDEX_MARGIN_WITHOUT_HISTORY` (100,000) past the highest key it
finds, instead of 1,000. Imported outputs are recorded at H's height
(their real heights aren't in the snapshot), which only matters for the
coinbase maturity of outputs younger than H.

## Consensus changes (summary)

1. Every block carries a chain proof (chain-step top level); `Proof`
   gains a kind (or the tree kind gains a chain layer).
2. The block statement gains the chain fields (`prev_hash`, roots,
   height, cumulative work, retarget state).
3. Probably: circuit-friendly state commitments (element hashing,
   small bitmap leaves, smaller depth), and possibly a duplicate-output
   rule the circuit can check cheaply.
4. Genesis handling (base case).
5. Wire: fetching the tip's proof and a snapshot.

## Open questions

- **State structure**: today's PMMR + bitmap re-hashed with elements, or
  a combined PMMR-with-spent-flags, or an indexed Merkle tree of
  unspent outputs? Decide by measuring rows per input and per output.
- **Duplicate outputs** (settled, 2026-10-08: not an issue -- there are
  no light clients; every node either validates every block or fast-syncs
  and then does): the no-duplicate-of-a-live-
  output rule isn't in the chain proof (it needs non-membership). Every
  node still enforces it: natively on every block it applies, and a
  fast-synced node on its snapshot (two unspent outputs alike are
  refused). All the proof leaves unchecked is a duplicate created *and
  spent* before the sync point, which can't affect the state. Making
  spends name a position (so duplicates are harmless) would put every
  rule in the proof, if that's ever wanted.
- **Block time** given the proving floor.
- **Chain step for direct proofs**: wrap every direct proof (one wrap
  circuit per trace size), or require tree-form contents for every
  block (a fixed chunk shape even for one transaction)?
- **Cumulative work in-circuit**: 256-bit arithmetic is fine; is
  exactness needed, or is a coarser measure enough for fork choice?
- **Old blocks**: a fast-synced node has no blocks below its snapshot,
  so it can't serve them. Since every node fast-syncs, old blocks are
  only needed by `--full-sync` nodes, which need an archival peer.
  (Archival nodes keep every active block today.)

## Spike results (2026-10-06, `state_circuit.rs`)

Both variants built in the circuit VM; roots checked against native code
(variant B against a native reference tree, variant A's primitives
against today's `hash_bytes`), constraints checked.

| | rows per input | rows per output |
|---|---|---|
| **B: fixed-depth state tree** (measured) | **2,122** | **2,122** |
| A: today's PMMR + bitmap (from measured primitives) | ~178,800 | ~2,600 |
| a block proof, for scale | ~13,100 (chunk rows / 10 inputs) | |

- Variant A's cost is the byte hashing: one PMMR node hash is **1,308
  rows** (decomposing two digests into bits and regrouping them into
  3-byte elements) against **32** for B's node, and a bitmap page update
  is **11,359 rows** (rehashing 4 KB, twice); with 49 bitmap levels on
  top, a spend costs ~84× B's.
- Variant B: 2 × 32 permutations per operation (verify the old path,
  compute the new one) plus ~74 rows of bit decomposition and repacking.
- **A 10,000-transaction block** (2.5 inputs, 2.5 outputs): B **106M
  rows**, A **4,535M rows**, against ~328M rows of block proofs.
- Time: circuit-VM rows prove at ~4,700 rows/s on the laptop (65,536
  rows in 13.9 s, tree parameters) -- block-circuit rows are wider, ~1,000
  rows/s (a 2^17 chunk in ~130 s). So B's state transition for a 10k block
  is ~22,000 laptop-seconds against ~325,000 for its chunk proofs: **about
  +7% work**. A would be ~965,000: about 3× the whole block.
- Not yet optimized: appends could use a frontier (no "old path" check:
  ~half), and spends in one block share their upper path nodes.

**Decision: variant B.** Today's PMMR + bitmap is not viable to prove;
a fixed-depth state tree with element hashing costs a few percent. It's
also the shape a circuit needs: every operation is the same whatever the
data.

## Steps

1. **Spike** -- done (above).: build the state-transition circuit for one block,
   alone: PMMR membership and append, bitmap check-and-set, roots in and
   out. Measure rows per input and per output for (a) today's
   structures as they are and (b) the circuit-friendly variant;
   extrapolate to 1k and 10k-transaction blocks. **This decides the
   state structure** -- before anything else is built.
2. **Switch the chain's state to the state tree** -- done (and then
   each leaf made to commit to the output's nonce, `leaf(commitment,
   nonce)`: +1 permutation per spend or append, 2,155 rows instead of
   2,122; wire version 7) --
   (`state_tree.rs`): one fixed-depth tree (32 levels, element hashing,
   one permutation per node) replaces the PMMR and bitmap; the header
   carries `state_root` and `output_count` (152 bytes, was 176); apply,
   unwind and block building use it, storing only non-empty nodes; the
   UTXO index (commitment -> position) still resolves spends and refuses
   duplicates of live outputs. Genesis re-mined; wire version 6. Tests:
   the stored tree matches the in-memory reference operation by
   operation, undo restores the exact previous state (root, count,
   storage), and every chain, reorg, network and end-to-end test passes
   on it -- including real proofs and wallet recovery.
3. **Chain step, milestone 1** -- done (`chain_step.rs`): a chain proof
   per header, verifying the previous header's chain proof in its
   circuit (or, at the bottom, a genesis circuit's proof of the genesis
   header), and checking the header against what that proof attests --
   it links, height + 1, timestamp strictly later (64-bit, limb by limb),
   and proof of work: the real header hash (Poseidon2 over its 152 bytes,
   byte gadgets from the spike) at most the target as a 256-bit number.
   Public inputs: step key, header hash, height and timestamp, target.
   Tests: genesis -> step -> step proves recursively and the last proof
   alone verifies; a different claimed height or hash fails; a header
   that doesn't link, or whose timestamp doesn't advance, can't be
   proven. **Measured with consensus parameters** (laptop CPU):

   | | |
   |---|---|
   | chain step | 128,031 rows -- 49% of 2^18 |
   | proving a step (the per-block floor, so far) | **57.5 s** |
   | proof | 120 KB, verified in 7.5 ms |
   | step key (once) | 12 s |
   | peak memory | 5.0 GB |

   Of the 128k rows, nearly all are the verifier for the child proof;
   the header checks are a few thousand. **Implication for milestone 2**:
   verifying a second proof (the block's contents) adds roughly another
   ~120k rows -- about 250k of 262k, so a step with both fits 2^18 with
   little room, and the **state transition can't be a third child** at
   this size (it would push the step to 2^19, about doubling the floor).
   The likely shape: prove the state transition inside the contents tree
   (per-chunk transition proofs aggregated with the chunk proofs), so one
   contents root attests both. To decide in milestone 2.

   Still to do in the chain step: retargeting (the target is carried
   unchanged so far), cumulative work, the contents proof, the state
   transition.
4. **Milestone 2: block proofs attest the state transition** -- done.
   A chain step can verify only one block proof besides its parent's,
   so one proof must cover contents *and* state. Option A (chosen): each
   chunk's **wrap applies the chunk to the state** -- it already holds
   the chunk's exact commitments and nonces, so contents and state are
   bound for free:
   - Wrap and aggregate proofs gained three public inputs (`root_in`,
     `root_out`, `[count_in, count_out]`); a wrap spends each used input
     slot's leaf `leaf(commitment, nonce)` at its (witness) position and
     appends each used output slot's leaf at the next position; unused
     slots are no-ops (`EMPTY` -> `EMPTY`); aggregation chains the left
     child's end to the right child's start.
   - **Chunk shape 8 inputs / 20 outputs** (was 10 / 256), also the
     per-transaction limit (wallet `MAX_INPUTS`, mempool, `plan_chunks`).
     Measured: the wrap is 202,999 rows, 77% of 2^18 (the smaller
     statement made its verifier cheaper, more than paying for 28 state
     updates) -- room to raise the output count later.
   - **Every block's proof is a tree** (a one-chunk block's root is its
     wrap); direct proofs are retired (kind 0).
   - **Outputs are appended in chunk order** (body order within each
     chunk): full nodes take the chunk assignment from the proof's
     header; `Chain::build_block` plans the chunks and records each
     chunk's state witness in the same pass (`BlockPlan`). *(Since
     2026-10-07: body order, with the assignment no longer published --
     `RECURSION.md`, "Privacy enhancements" #1.)*
   - Proof verification moved from `Block::validate` into the chain's
     apply, which knows the parent's `(state_root, output_count)`.
   - Verified: unit and circuit tests; `tree_keys` with consensus
     parameters (a two-chunk block proved in 505 s, 120 KB, verified in
     8.3 ms; altered lists, totals, state or nonces refused); a live run
     -- two nodes mined to height 12 and made a payment (2026-10-06).
   - Cost: every block now pays a chunk proof (~140 s on the laptop)
     plus a wrap (~60 s) even when empty -- ~3.3 min; each further chunk
     of 8 inputs adds a chunk, a wrap and an aggregation.
   - **Dev network** (`network.rs`, `--network dev`), for testing at
     this cost: light, insecure proof parameters (blowup 4, 8 queries -- 4 since
     2026-10-07,
     no grinding) and half-size tree proofs (2^17 rows; the wrap is
     127,114 rows, 97%), with its own verifying keys, genesis, wire magic
     (`TBRD`, so dev and main nodes never talk), default data
     directory (`~/.tabernacle/dev`), and shorter wallet waits: rewards
     mature after 3 confirmations and recovered outputs are held 3 blocks
     (main: 10 each). Measured: a two-chunk block in
     140 s (main: 505 s), 47 KB proof, verified in 3.2 ms, 2.1 GB peak;
     live, two nodes produced a block every ~70 s (main: ~3.3 min+).
5. **The chain step, completed** (`chain_step.rs`, `chain_rules.rs`):
   - **5a -- the block's proof** (done): each step also verifies the
     block's tree root (by the wrap or aggregation key), checks it
     claims exactly the reward, and that it moves the state from the
     parent's attested root and count to the header's `state_root` and
     `output_count`. A chain proof now vouches for every block's full
     validity, not just its header.
   - **5b -- retargeting and cumulative work** (done): the statement
     carries the retarget window's start and the cumulative work; each
     step applies the retarget rule (`chain::next_retarget`, shared with
     the node) and adds the block's work (`pow::work_for_target`), as
     256-bit arithmetic over byte limbs with witness quotients
     (`chain_rules`). Gadget tests check both against the native
     functions across window positions, clamped, backwards and
     overflowing windows.
   - Tested on dev: genesis -> two real proven blocks, recursively; any
     other claimed height, hash, output count, state root, target,
     window start or work fails; a header that doesn't link, another
     block's proof, a timestamp that doesn't advance, or extra claimed
     work can't be proven.
   - **Measured**:

     | | rows | step proof | size | verify |
     |---|---|---|---|---|
     | dev | 110,752 of 2^17 (84%) | 12.2 s | 47 KB | 3.0 ms |
     | main | **260,399 of 2^18 (99%)** | 65.5 s | 120 KB | 7.6 ms |

     Main has ~1,700 rows to spare: any further check in the step needs
     room made first (e.g. reusing the PoW check's bit decompositions).
   - Still not proven in the step: rejecting a duplicate of a live
     output (open question), and the future-timestamp rule (can't be).
6. **5c -- chain proofs in consensus** (done):
   - **Every block after genesis carries its parent's chain proof**
     (`BlockBody::chain_proof`; block 1 carries the genesis circuit's
     proof). It can't be in the parent itself, which it attests nonce
     and all. Body format version 3; genesis re-mined on both networks;
     wire version 8.
   - **Validation**: a chain that requires them (`Chain::
     require_chain_proofs`; every node does, tests opt in) verifies a
     block's chain proof against the parent *as it records it* -- hash,
     height, timestamp, state root and count, target, window start, work
     (`Tip`) -- for active-chain and side-branch blocks alike.
   - **Production**: everything a chain proof needs is chain data
     (`Chain::chain_proof_inputs`: the block's header and body, its
     parent's tip, the parent's chain proof from the block's own body),
     so any node can make one. The miner makes the tip's when it builds a
     template (cached per tip), then the block proof; `ChainProver`
     derives its proving keys the first time (the genesis circuit's from
     the genesis tip, the step's from block 1) and the node checks every
     chain proof against the network's constants (`consensus_verifier`).
   - **Keys**: the genesis and step circuits' caps are per-network
     consensus constants (`chain_step`), regenerated by `main`'s
     `chain_keys` test.
   - Tested (`e2e::chain_proofs_as_consensus`, dev): a chain requiring
     chain proofs accepts four real blocks -- the genesis proof, then step
     proofs -- and refuses a block carrying another block's chain proof.
     Chain proof 10-13 s, block proof ~62-67 s per block (dev, laptop).
7. **5d -- fast sync** (done; see "Fast sync" above):
   - **State tree** (`state_tree.rs`): unspent outputs' leaves kept by
     position (to serve); views as of an earlier block from the current
     tree plus undo data (`AsOf`); `import` from a snapshot, fully spent
     subtrees stored as their root alone.
   - **Pieces** (`snapshot.rs`): what they are, how each is checked, and
     the download plan.
   - **Chain** (`chain.rs`): `StateReader` serves sync points and pieces;
     `check_sync_point` and `import_snapshot` start a chain at H, with
     the reorg floor at H and `has_full_history` false.
   - **Network**: wire messages `GET_SYNC_POINT`/`SYNC_POINT` and
     `GET_PIECE`/`PIECE_CHUNK` (version 8); `statesync.rs` serves and
     downloads pieces from all peers, banning bad senders; `transfer`
     pauses block-by-block sync and fetches blocks H and H+1 by height.
   - **Node** (`fastsync.rs`): the steps above, on by default for a node
     with nothing but genesis (`--full-sync` to replay instead,
     `--sync-depth` for the depth); no mining until done.
   - Tested: `state_tree` import and as-of views; `snapshot` piece
     checks (tampering refused, fully spent pieces skipped);
     `chain::fast_sync_from_a_state_snapshot` (import, catch up to the
     same state, serve it on, refuse anything below H);
     `net::a_fresh_node_downloads_the_state_from_two_peers` (UDP, two
     peers at once); live on dev.
8. **Storage** (done): a node stores a state-tree node only if its
   subtree holds two or more unspent outputs (and never below level 4);
   the rest is recomputed from the leaf records. The UTXO index and the
   output index share one record per output. Measured
   (`chain::snapshot_storage_cost`, 1M unspent outputs): **~200 B per
   unspent output on disk after a fast sync** (161 B at 50% of outputs
   unspent, 201 B at 10%, 208 B at 1%), down from 0.67-1.7 KB; the
   download is ~53 B. Data in the old layout is refused (storage
   version 2).
9. **128-bit main** (done): blowup 16, 26 queries, 24 grinding bits --
   128 bits conjectured, ~64 against Grover. Each query costs ~5.9k rows
   per verified proof, so a circuit verifying two proofs needs ~345k
   rows: every tree proof is 2^19. Measured on a 12-thread laptop:
   one-chunk block proof ~296 s (157 s of it the chunk), 161.9 KB,
   verify 10.3 ms, peak 7.8 GB; chain step 344,911 rows (66%), proof
   148.6 s, 161 KB, verify 10.2 ms, peak 9.9 GB. Dev is unchanged.
10. **Ten-minute blocks, ASERT, the reward schedule, the aux hash**
   (done, 2026-10-07):
   - **Main's target block time is ten minutes** (dev's unchanged).
   - **Retargeting is ASERT** (Bitcoin Cash's aserti3-2d, replacing
     Bitcoin's window rule; `chain::asert`): every block's target is the
     first block's, times `2^(behind / half_life)`, `behind` being how
     far the block's timestamp is past the schedule (the first block's
     timestamp plus a target block time per block since), with
     aserti3-2d's integer arithmetic (a cubic for the fractional power)
     and clamped to `[1, 2^256 - 1]`. Half-life: two days on main (288
     blocks), ten minutes on dev. It adjusts every block, and needs no
     window: the retarget state is just the first block's timestamp,
     carried in the chain proof where the window start was. The gadget
     (`chain_rules::retarget`) offsets `behind` by a multiple of the
     half-life to keep it non-negative, checks the division and the
     cubic in bytes, and shifts by a small multiplier plus a 7-stage
     byte barrel shifter; it's tested against the native rule at every
     clamp and shift boundary. Dev's chain step is 82,225 rows (63% of
     2^17).
   - **The reward follows a schedule** (`prover::Schedule`): on main
     1,000,000,000 a block for seven years (`7 × 144 × 365` blocks),
     then 7,000,000 for a thousand -- each era issuing 367,920,000,000,000
     -- and no block is valid from height `1007 × 144 × 365` on. Dev pays
     `REWARD` forever. Validators check a block's proof against the
     reward at its height; the chain step selects it from the height's
     (now canonical) bits and refuses heights past the end.
   - **The state tree is 40 levels deep** (2^40 positions, a thousand
     years of full blocks); positions and counts are two 20-bit limbs in
     the circuits, the chain proof's output count included. Snapshot
     pieces start at level 40.
   - **The header carries `aux_hash`** (32 bytes after `body_hash`, 184
     in all): any value the miner chooses, no meaning to consensus,
     covered by proof of work and hashed in the chain step. Zeros for
     now. Wire version 10; geneses and all keys regenerated.
   - **Dev proofs use 4 queries** (was 8): the deeper tree's paths took
     dev's wrap to 144,393 rows, over its 2^17; at 4 queries it's
     122,913 (94%). Main's wrap fits its 2^19 as before.
11. Next: proving ahead (pipelining), and reconsidering the remaining
   optimizations.
7. (Earlier plan.) The chain-step circuit, completed: verify parent chain proof + contents proof +
   transition proof; parent header checks (PoW, link, timestamp,
   retarget, work); genesis base case. Measure the per-block floor.
4. Consensus: blocks carry chain proofs; miners prove the chain step
   when a parent arrives (contents and transition proved ahead).
5. Snapshots and fast sync over the network.
6. End to end: a fresh node syncs from the tip alone, then follows the
   chain; recovery works on it.

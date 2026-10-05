# Recursion: design proposal

Status: **agreed; in progress.** Steps 1–4 of "Suggested order" are done.

## Why

The goal is blocks of 5,000–10,000 transactions (see the scale target in
`docs/BLOCK_TODO.md` #1). Today a block is one STARK proof of one trace,
and that cannot scale:

- Each spent input costs ~260 Poseidon2 permutations (224 WOTS chain
  steps, 33 public-key sponge blocks, digit derivation, commitment).
  10,000 transactions at ~2 inputs each is ~5 million permutations.
- One trace over BabyBear is capped at 2^27 extended points, i.e.
  2^20 rows at blowup 16 — about 125 inputs in today's layout, and
  still only ~4 million permutations even at one permutation per row and
  minimal blowup.

So a block's proof must be built from many smaller proofs: **chunk
proofs**, proven independently (on separate cores, machines, or — one
day, not by us — GPUs), then combined by **aggregation proofs** that
verify other proofs inside a circuit. Only the final aggregation proof is
published, and its size and verification time are essentially independent
of block size. That's also exactly where the "small proofs, fast
verification" priority applies.

Nothing here changes what a block *means*: the published statement is
still "these input/output commitment lists, this reward, balance and
authorization hold" (`block_air`'s statement). Chunking and aggregation
are the prover's business; consensus checks one proof against the
block's public lists.

## Overview

```
 block's transactions
        │  split by the miner
        ▼
 ┌─────────┐ ┌─────────┐       ┌─────────┐
 │ chunk 0 │ │ chunk 1 │  ...  │ chunk k │   block circuit, one trace each,
 └────┬────┘ └────┬────┘       └────┬────┘   tuned for prover throughput
      └─────┬─────┘                  │
        ┌───▼───┐                    │        aggregation circuit:
        │ agg   │       ...      ┌───▼───┐    verifies 2 proofs (chunk or
        └───┬───┘                │ agg   │    aggregation) per proof
            └────────┬───────────┘
                 ┌───▼───┐
                 │ root  │  ← published: blowup 16, ~100 KB, ~10 ms
                 └───────┘
```

## Pieces

### 1. An algebraic transcript (prerequisite)

Fiat-Shamir currently hashes *bytes* (`transcript.rs` over `hash_bytes`:
labels, caps and extension values serialized to bytes, query indices
taken from squeezed bytes). An aggregation circuit has to re-run the
inner proof's transcript, and byte handling in-circuit is expensive.

Proposal: rebuild `Transcript` as a duplex sponge over Poseidon2
*elements* — absorb field/extension elements and digests directly, domain
labels as small constants, challenges squeezed as elements, query indices
taken from the low bits of a squeezed element (bit-decomposed in-circuit).
Every proof format changes once (chain data gets wiped, as before).

### 2. Chunked block proofs with global challenges

The block circuit's bus (LogUp) and balance are block-wide: a
transaction's inputs, outputs, and message may land in different chunks.
Chunks are tied together like this:

1. **Commit all chunks first.** Each chunk commits its main trace (Merkle
   cap) as usual.
2. **Draw global challenges** — the bus's `gamma`/`beta` — from a
   transcript over the public statement and *every* chunk's cap, in order.
   No chunk's witness can then be chosen knowing the challenges.
3. **Finish each chunk proof** with those challenges: auxiliary columns,
   composition, FRI — independently, in parallel.
4. Each chunk exposes, as public outputs: its main-trace cap, its share of
   the bus sum, and its share of the running balance (the five limbs).
5. The aggregation layer checks: the global challenges really were derived
   from all the chunks' caps; the bus shares sum to what the public lists
   require; the balance shares plus the reward net to exactly zero.

What stays inside a single chunk: an input's whole section (digit
derivation, chains, public-key sponge, commitment) and a transaction's
message sponge. What may cross chunks: anything on the bus (commitments
into messages, messages to signature checks, commitments to the public
lists). Section-local bus tags (digits, chain tops) gain the chunk's index,
so two chunks' sections can never be confused.

This is the one step that needs a two-round prover (commit all, then
finish all) — but it's entirely prover-side: a verifier only ever sees the
root proof.

### 3. Constraints as data: symbolic evaluation

To verify a proof, the verifier evaluates the inner AIR's constraints at
the out-of-domain point `z`. In-circuit, that means the aggregation
circuit must run *some specific AIR's* constraints in extension-field
arithmetic.

`Air::eval_transition` is already generic over `Field`. Implementing
`Field` for a *symbolic expression* type records every constraint as an
expression graph, which compiles to a fixed straight-line program of
extension-field operations — run by a small "extension arithmetic" section
of the aggregation circuit. No AIR needs rewriting by hand to be
verifiable, and a change to the block circuit automatically changes what
the aggregator checks.

### 4. The aggregation circuit

One AIR that verifies two proofs, each either a chunk proof or an
aggregation proof — so trees of any shape and any number of chunks work
with one circuit. Per verified proof it:

- replays the transcript (Poseidon2 chip, from piece 1);
- checks the grinding nonce;
- evaluates the inner AIR's constraints at `z` (piece 3) and compares to
  the stated composition value;
- for each query: verifies the trace/aux/composition Merkle openings
  against the caps (Poseidon2 chip: leaf hashes, node hashes), recomputes
  the DEEP value from the opened rows, and checks the FRI folding path —
  extension-field folds, round openings, the final value;
- carries the inner proof's public outputs (caps, bus/balance shares) up,
  combining the two children's.

Which AIR a child proof is of is identified by a *verifying key* — a hash
of that AIR's shape, constraint program, and parameters — passed as a
public input and checked against the two allowed ones (chunk,
aggregation). The root proof's verifying key is a consensus constant.

Rough cost per verified proof (20 queries, blowup 16): ~2–4 thousand
Poseidon2 permutations (dominated by leaf hashes of wide trace rows and
FRI paths) plus a few thousand extension-field operations. Note that
inner trace *width* drives this directly: every opened row is hashed
in-circuit. That's why narrowing the block circuit (deferred earlier)
returns here, applied to the chunk layer.

### 5. Parameters per layer

- **Chunk proofs:** never published. Tuned for prover throughput: low
  blowup (2–4), dense layout. Their proof size matters only through
  aggregation cost.
- **Aggregation proofs (inner):** moderate parameters.
- **Root proof:** blowup 16, 20 queries, 20-bit grinding — the current
  `prover::PARAMS` — for the smallest published proof and fastest check.

The verifier of a block checks only the root.

## Scaling check

10,000 transactions ≈ 5M permutations of chunk work. At one permutation
per row (a dense chunk layout), ~2^22-row chunks hold ~4M permutations, so
a handful of chunks — or many small ones, for parallelism — plus a few
levels of aggregation. Each aggregation proof verifies two children at a
few thousand permutations each, so the aggregation tree is cheap relative
to the chunks. Nothing in this structure caps block size: more
transactions means more chunks and one more tree level per doubling, while
the published proof stays the same size.

## Suggested order

1. ~~Algebraic transcript~~ — **done**: `transcript.rs` is a duplex
   sponge over Poseidon2-24 elements (rate 16); labels are single
   constant elements, indices are low bits of a sampled element, grinding
   nonces are field elements.
2. ~~Symbolic constraint evaluation~~ — **done**: `symbolic.rs` (`Expr:
   Field`, `compile(air) -> Program`, `Program::eval`/`stats`/`digest`).
   Aux constraints are now generic over `Field` too. The block circuit
   compiles to 2,595 nodes (~1,030 extension multiplications, ~1,100
   additions), checked equal to direct evaluation at a random point.
3. ~~Aggregation circuit verifying *one* block proof~~ — **done**, as
   three pieces:
   - **Preprocessed columns** in `stark` (`Preprocessed`, `Air::preprocessed`):
     fixed public columns committed once; their cap is in the statement.
   - **A circuit VM** (`circuit.rs`): computations written against a
     `Builder` become one trace. Memory cells (an octet, or an extension
     element) are written once and read any number of times, matched by
     one LogUp bus over `(address, 8 lanes)`. Row kinds: Poseidon2 (32
     rows; reads 3 octets with an optional Merkle swap bit, writes 3),
     extension arithmetic `c = α·ab + β·a + γ·b + δ·d + Σλ_l·d[l]`,
     repack (octet ↔ two halves; also how witness values enter), bit step,
     and lookup at a computed address. The wiring (kinds, addresses,
     coefficients) is the preprocessed columns: 52 witness + 30 fixed
     columns, 4 bus slots.
   - **The verifier as a circuit** (`recursion.rs`): mirrors
     `stark::verify` exactly — transcript, constraint program at `z`
     (from step 2), DEEP via one Horner sum per opened row, Merkle paths
     with swap bits and cap lookups, FRI folds with slot lookups,
     canonical 31-bit index decompositions, grinding. The inner statement
     is the circuit's public input.

   Two format changes made the in-circuit transcript and Merkle leaves
   cheap: the transcript moves in whole octets (labels and data padded),
   and Merkle leaves hash with `hash_octets` (overwrite-mode sponge over
   octets, length in the capacity).

   Measured, verifying a reward-only block proof made at the consensus
   parameters: 1,739 permutations + 22,751 other rows (2^17 rows after
   padding). Proving that circuit at blowup 2 / 84 queries: ~17 s,
   393 KB, 28 ms to verify. At the consensus parameters (blowup 16):
   ~131 s (plus ~62 s to commit its fixed columns, a one-time cost per
   circuit), **120 KB, 9.6 ms to verify** — the same size and speed as a
   direct block proof, as it will stay however large the block.
4. ~~Two-proof aggregation and verifying keys~~ — **done** (`aggregate.rs`).
   Every tree proof has one trace length and parameter set and the public
   inputs `[vk, data]`. Wrap circuits verify one block proof
   (`data = H(statement)`); aggregation circuits verify two tree proofs
   (`data = H(data₁, data₂)`). A child's key is the hash of its
   preprocessed cap and must be the wrap key (built in) or the `vk` input
   (A's own key, which A can't build in without circularity; A children
   must carry the same `vk`, and the root verifier checks it). Supporting
   changes: the statement is absorbed in aligned parts (shape,
   preprocessed cap, public), constants moved into fixed columns (a
   constant row kind), public inputs sit at fixed addresses read once, and
   `RecursiveAir` statements are laid out from their bus tuples so a
   verifier circuit hands the child's statement back as cells.

   Measured with one-spend blocks (12-core laptop): the block proof at
   consensus parameters is 119 KB / 8 ms to verify / ~38 s to prove; a
   wrap circuit verifying it (2^17 rows) proven at consensus parameters is
   120 KB / 8 ms / 130 s (+27 s one-time key). Aggregating two wraps at
   light tree parameters: ~18 s per wrap or aggregation, 3.4 ms root
   verification. A secure aggregation layer needs 2^18-row circuits at
   blowup 16, beyond this machine's 22 GB with today's memory layout
   (Merkle trees keep every leaf; LDEs are kept whole).
5. Chunking with global challenges and the shares checks.
6. Revisit the chunk layout (dense/narrow) with real aggregation costs in
   hand.

## Open questions

- **Aggregation circuit layout.** Its own trace is mostly Poseidon2 (as
  is the block circuit's), so the same layout question — one round per
  row vs. denser — applies; decide with measurements in step 3.
- **Chunk boundaries.** Whole transactions per chunk would avoid
  cross-chunk messages entirely, at the cost of uneven chunks for very
  large transactions; the bus-based design above allows either.
- **Height / previous-block binding.** The root proof could later also
  attest chain-level facts (timestamps, the previous proof) for light
  clients — the "whole chain in one proof" recursion. Out of scope here,
  but the aggregation circuit's design (verifying aggregation proofs)
  is the same mechanism.

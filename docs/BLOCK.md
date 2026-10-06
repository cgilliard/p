# Block design

This pins down the shape of `Block` before any of it gets written. Status:
**decided** — the three open questions from the first draft (nonce width,
the fixed difficulty value, and how `Block` relates to `Transaction`) are
all resolved below.

> **Since then** (2026-10-06): the PMMR + bitmap state was replaced by one
> fixed-depth state tree (`state_tree.rs`, `docs/CHAIN_RECURSION.md`), so
> the header carries `state_root` and `output_count`; the header also
> gained `height` and `timestamp`; outputs carry recovery nonces; and the
> proof now covers signatures as well as balance. The sections below are
> updated where they describe the current code.

## Header

```rust
pub struct BlockHeader {
    pub prev_hash: [u8; 32],
    pub state_root: [u8; 32],
    pub body_hash: [u8; 32],
    pub output_count: u64,
    pub height: u64,
    pub timestamp: u64,
    pub nonce: [u8; 32],
}
```

- `prev_hash` — links to the previous block. Nothing validates this against
  an actual chain yet (there's no chain/sync data structure), so for now
  it's just a field that gets hashed and checked for PoW. Validating it
  against real history is later work.
- `state_root` / `output_count` — the *claimed* state after this block's
  updates are applied: the root of the state tree (every output ever
  created, by position: its commitment while unspent, then `SPENT`) and how
  many outputs it holds. Checked by actually applying the block's inputs
  and outputs to the real `StateTree` and comparing (see Validation below)
  — not merely stored.
- `body_hash` — commits to the body (next section), but **not** the proof.
  Same reasoning Bitcoin's segwit uses for excluding witness data from the
  txid: the body is the economic content (who pays whom, how much); the
  proof is validity evidence about that content, generated potentially
  after the body is fixed, and swapping in a different (equally valid)
  proof for the same body shouldn't require redoing anything that commits
  to the body itself.
- `nonce` — **`[u8; 32]`, confirmed.** `pow.rs`'s `pow_hash`/`verify`/`mine`
  are widened to take `[u8; 32]` instead of `u64`; `mine`'s search loop
  still just increments a `u64` counter internally and encodes it into the
  low 8 bytes of the 32-byte field each attempt (rest zero) -- no change to
  how mining actually works, just to the field's on-the-wire width.

### Difficulty is not a header field

No `max_hash` field on the header. It's a single fixed constant every block
uses, owned by `block.rs` (not `pow.rs`, which stays a generic mechanism
agnostic to what target any particular caller picks):

```rust
/// First byte zero, the rest maxed out -- a candidate block hash meets
/// this target iff its own first byte is exactly zero, which happens for
/// a uniformly random hash with probability 1/256. Picked to be mineable
/// in a reasonable number of attempts during development while still
/// actually exercising the PoW check, rather than being vacuous.
const FIXED_MAX_HASH: [u8; 32] = {
    let mut b = [0xffu8; 32];
    b[0] = 0x00;
    b
};
```

Real difficulty adjustment is later work, once there's a notion of block
height/timestamps to retarget against.

### `block_hash`

A block's own hash — what the *next* block's `prev_hash` would point to —
is just `pow::pow_hash(header_bytes, nonce)`, the same hash already
computed while mining it. No separate hash needed.

## Body

Two flat, canonically-sorted lists — not a list of transactions:

```rust
pub struct BlockBody {
    pub inputs: Vec<(PublicKey, u64)>,  // sorted ascending by pubkey bytes
    pub outputs: Vec<Output>,            // sorted ascending by output bytes
}
```

- Inputs sorted ascending by public-key bytes, outputs sorted ascending by
  their own encoded bytes — the exact same canonical-ordering convention
  `Transaction::add_input`/`add_output` already use, just applied across
  *every* transaction in the block at once rather than within one. Picking
  the same key `Transaction` already uses (rather than, say, each input's
  resolved state-tree position) means the body's canonical order doesn't depend
  on first resolving anything through the `utxo` index — it's intrinsic to
  the data itself.
- No per-transaction grouping survives in this representation. This is
  deliberate: it's the data-availability payload from early on in this
  project's design discussion — "the prover also discloses the
  inputs/outputs that were proven" — and a block's `body_hash` should
  commit to exactly that payload, nothing about *how* it was assembled.
- `body_hash = Poseidon2(serialize(sorted inputs) || serialize(sorted outputs))`,
  mirroring `Transaction::signing_message`'s own byte layout.

### Signatures are not `Block`'s concern, now or later

`BlockBody` has no signatures in it, and `Block` has no `transactions:
Vec<Transaction>` field at all -- authorization is entirely the proof's
job, today and after it eventually grows to cover it. Until then,
`Block::validate()` simply does not check that spent inputs were actually
authorized; that's an accepted, explicit gap, not an oversight, matching
how the proof's own scope is being grown incrementally.

This drops `transaction.rs` out of `block.rs` entirely. `Transaction`
remains a useful standalone primitive for off-chain coordination --
a wallet or a multi-party exchange uses it to gather signatures before a
miner ever sees anything -- but a miner assembling a block just reads each
already-signed `Transaction`'s `(pubkey, amount)` inputs and `Output`s
straight into the flat `BlockBody`, discards the signatures, and the
signatures' validity becomes something the *prover* will need to establish
as private witness data when the authorization-covering proof eventually
exists. Nothing here re-verifies them in the meantime.

## No coinbase transaction, just an unbacked output

Without transaction grouping, there's no "zero-input transaction" to
detect anymore. Whoever assembles the block just adds however many extra
outputs they like, to themselves, worth up to the total of
`BLOCK_REWARD` plus whatever the block's other inputs/outputs leave
unclaimed -- the flat balance equation (`sum(outputs) == sum(inputs) +
BLOCK_REWARD`) is the only thing constraining it, same as before, just
with no special-casing needed to recognize which output *is* the claim.

## Proof

Scope, per the decision already made: **the proof only attests to the
balance equation for now** — nothing about signatures, nothing about the
`Pmmr`/`Bitmap` transition being correctly applied. Those stay checked the
non-succinct way (directly, in Rust) until the proof's scope grows to cover
them, which is separate, later, multi-step work (trace → constraints →
quotient → composition → the existing `fri` commit/query machinery).

Excluded from `body_hash` and from `header_bytes` (so PoW doesn't need to
be redone if the proof changes without the body changing).

## Validation (the non-succinct reference)

What `Block::validate()` checks:

1. **PoW** — `pow::verify(header_bytes, nonce, &FIXED_MAX_HASH)`.
2. **Body commitment** — recompute `body_hash` from the stored `BlockBody`
   and check it matches the header's.
3. **Balance** — `sum(outputs) == sum(inputs) + BLOCK_REWARD`.
4. **State transition** — for each input, resolve its commitment to a
   position via `UtxoIndex` (present only while unspent), then (in a write
   transaction that only commits if everything checks out) set that
   state-tree leaf to `SPENT` and remove the `UtxoIndex` entry; for each
   output, refuse a duplicate of a live one, append it to the state tree
   and insert its `UtxoIndex` entry. Finally, check the resulting state
   root and output count match the header's `state_root`/`output_count`.
5. **No double-spend within the block** — falls out of step 4 automatically:
   a second input trying to spend the same output will find the
   `UtxoIndex` entry already removed by the first.

**Explicitly not checked, by design, until the proof covers it:** that any
spent input was actually authorized by its owner. See above.

## Explicitly out of scope for this round

- Difficulty retargeting, block height, timestamps.
- Validating `prev_hash` against actual chain history (no chain structure
  exists yet).
- Authorization (signature) checking of any kind -- entirely deferred to
  the proof, once its scope grows to cover it.
- Any part of the proof beyond the balance equation.

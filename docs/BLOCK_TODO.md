# Block/chain TODO

Gaps identified after `chain.rs`/`block.rs`/`prover.rs` (stub) were wired
together and verified end-to-end (`e2e.rs`: a miner mining two blocks,
paying another user, the recipient spending onward, a double-spend
correctly rejected). The pipeline itself works. These are the things
still missing before it's a real chain, roughly ordered by how much they
matter — the first is worth settling on paper *before* the real ZK
circuit gets built, since the circuit's job is enforcing exactly that
rule, and building it against an unspecified rule means redoing it.

## 1. No economic enforcement (unbounded minting) -- this *is* the proof

**Status:** not started. This is the real proof's core job, not a
separate task alongside it.

**Note on scope:** the proof's job isn't just hiding amounts/pubkeys --
the goal is a *recursive* proof, so a light client (or new node) can
verify one constant-size proof and trust the entire chain back to
genesis, without downloading or replaying any of it. That means any
per-block rule that only gives a *whole-chain* guarantee once composed
recursively belongs here too, not just the rules that need hidden data.
Timestamp monotonicity (see #3) is exactly that shape -- it's fully
public data, so it's not here for privacy reasons, but a plaintext
`chain.rs` check of it only helps a full node replaying every block
directly; folding "my timestamp >= the previous (already-verified)
timestamp" into each recursive step is what lets a light client get the
same guarantee for free. (The future-bound timestamp check, by
contrast, can *never* be part of any proof -- see #3.)

Nothing anywhere checks that total output value is bounded by block
reward. Concretely, *today*, a block can contain any number of
zero-input "reward" transactions, minting any amount to any pubkey, and
nothing rejects it. This can't be fixed with ordinary plaintext
plumbing *at all* -- the chain only ever sees opaque commitments, never
the amounts behind them, so there is nothing for plaintext code to sum.
Checking this is exactly, and only, what the ZK proof is for.

This also subsumes fees as a separate concept (an earlier version of
this doc tracked "no fee mechanism" on its own). There's no need for a
dedicated fee field or convention: if the circuit checks the balance
equation across the *whole block* --

```
sum(all inputs in the block) + block_reward == sum(all outputs in the block)
```

-- then a transaction whose inputs exceed its outputs simply leaves
slack in that equation, which the miner's own reward output can be
sized to absorb. That slack *is* the fee; it falls out of the one
equation for free, with no separate mechanism.

What the circuit needs pinned down:

- A fixed (or schedule-based, see #3) block reward amount.
- A rule for how many reward-claiming transactions a block may contain
  (exactly one?).
- The one balance equation above.
- Timestamp monotonicity: `header.timestamp >= previous_header.timestamp`,
  checked at each recursive step against the previous (already-verified)
  timestamp -- see the scope note above and #3.

What's still ordinary (non-proof) plumbing, once the circuit exists:
the miner needs to compute `sum(their plaintext inputs) -
sum(their plaintext outputs) + base_reward` themselves, in plaintext
(they have full visibility into their own candidate transactions), to
know how big to make their own reward output *before* asking the
circuit to confirm they got it right. Trivial arithmetic over data
they already have -- not a design question, just a small helper
somewhere in the build pipeline once there's a real circuit to feed.

## 2. No fork handling

**Status:** mostly done -- side branches, fork-choice by cumulative
work, bounded reorgs, orphans, and invalid-block tracking are in
`chain.rs` (`Chain::accept_block`). See `FORK.md` for what's done and
what's still open. `powLimit` (below) is not started. The original
description follows.

`Chain::apply_block` only accepts a block whose `prev_hash` matches the
*current* tip (see `chain.rs`'s `WrongParent` check) — there's no notion
of a competing block, an orphan waiting on a missing parent, or
switching to a heavier chain. Not implemented *yet* because there's no
networking layer to actually receive a competing block from -- not
because the goal is staying single-miner. This is the real blockchain's
consensus layer; it's next, not skipped. Needs:

- Storing blocks that don't extend the current tip instead of just
  rejecting them.
- A fork-choice rule (heaviest/longest chain) -- needs #3 (height or
  cumulative work) to compare candidates.
- Reorg: unwinding `pmmr`/`bitmap`/`utxo` back to a common ancestor and
  reapplying the new best chain.
- `powLimit` (a network-wide ceiling on how easy the PoW target is ever
  allowed to become, independent of plain integer saturation): real
  purpose, not legacy cruft -- bounds how far retargeting can degrade
  security after a pathological stretch (a long gap with no miner, or
  adversarial timestamps) once there's an actual network of
  independent, potentially absent or adversarial miners to defend
  against. Needs sizing against real behavior once there's a network
  to observe, so it belongs here, sequenced after this item, not
  bundled into retargeting (`chain::DifficultyConfig`) in isolation.

## 3. No block height or timestamp

**Status:** done. Timestamp enforcement split across two homes, for a
reason worth remembering: one piece can recursively compose into the
proof, the other structurally never can.

- **Height *is* a header field after all** (`BlockHeader::height: u64`,
  covered by PoW) -- the original reasoning for leaving it out ("fully
  recoverable by walking `prev_hash`") only holds for a full node that
  already has the whole chain. A light client verifying a single block
  or recursive proof, without downloading the rest, has nothing to
  walk -- it needs height to be self-contained, verifiable data on the
  block itself, same as everything else PoW covers. `Chain` still
  independently tracks and checks it (`Error::WrongHeight` if a new
  block's claimed height isn't exactly one more than the current tip's)
  so a full node catches a bad claim immediately, same spirit as
  re-deriving `pmmr_root`/`bitmap_root` rather than trusting them.
  `chain_meta` stores the tip's one full header now (`tip_header`,
  under `TIP_HEADER_KEY`) rather than separate `tip_hash` +
  `next_height` scalars -- `tip_hash()`/`height()` both just derive
  from it, so there's no longer two independently-updated pieces of
  tip metadata that could drift out of sync with each other.
- **Timestamp** *is* a header field too: `BlockHeader::timestamp: u64`
  (Unix seconds), stamped with the current time in
  `UnprovenBlock::finish` and included in `pow_preimage` (so it can't
  be altered post-mining without redoing the proof of work, same as
  every other committed field). `HEADER_LEN` grew from 160 (original)
  to 176 bytes across both additions (160 → 168 for `timestamp`, then
  168 → 176 for `height`).
- **Future-bound check: implemented**, in plaintext, in
  `Chain::apply_block`: rejects (`Error::TimestampTooFarInFuture`) a
  header whose `timestamp` is more than `MAX_FUTURE_DRIFT_SECS` (2
  hours, Bitcoin's order of magnitude) ahead of this node's own clock
  (`block::now_unix`). This rule can **never** move into any proof,
  recursive or not -- it's a statement about the relationship between a
  timestamp and whenever *this particular check* runs, not a fact fixed
  at proving time. Every verifier checks this locally, against its own
  clock, no matter how much of the rest of chain validity eventually
  gets folded into a recursive proof.
- **Monotonicity check: deferred to the proof**, folded into #1 instead
  of implemented here in plaintext. Unlike the future-bound check, this
  one *is* a fixed, recursively-composable fact (each header's
  timestamp relative to the one before it), so it belongs in the same
  place the balance equation does -- see #1's scope note.

This also settles #1's dependency on a schedule-based reward (height
is now available to key a reward-halving schedule off of, whenever #1
gets built) and #2's need for a cheap tip-height comparison (now
available via `Chain::height`, though the harder part of #2 --
choosing between two competing chains, not just reading one's height
-- is still unstarted).

## 4. No wallet / payment-detection story

**Status:** not started.

`e2e.rs`'s test works because the sender is handed the recipient's
pubkey directly, in-process. A real recipient has no way to notice "a
payment landed for me": outputs are opaque `H(H(pubkey) || amount)`
commitments, so nothing short of being told the exact commitment (or
trial-checking candidates against known pubkeys/amounts) reveals it.
The "recipient hands the sender a fresh pubkey out of band" flow was
discussed conceptually (see the Grin-comparison discussion) but neither
side of that handoff has any code. Needs:

- A wallet type that holds keys (plausibly HD-derived, to get a fresh
  pubkey per expected payment without manual bookkeeping).
- Some mechanism (even an out-of-band one, like Grin's) for a sender to
  learn the recipient's next pubkey.
- A way for a wallet to notice which `pmmr`/`utxo` entries are actually
  its own, once it knows which (pubkey, amount) pairs it's expecting.

## 5. No real driver

**Status:** not started. Expected at this stage, not urgent.

`main.rs` still just prints "Hello world!". No CLI, no mempool, no
persistent/interruptible mining loop (today's `block::mine_block` just
takes a bounded attempt count for tests), no networking. This is the
difference between "a tested library" and "a thing you can run."

## 6. No pruning

**Status:** not started. Low urgency.

The PMMR is "prunable" by name only -- nothing ever removes spent-output
data, so storage grows forever. `bitmap` already tracks spent status
per position, which is the piece pruning would need; the actual removal
logic (and deciding what "removal" even means under LMDB, which doesn't
shrink files automatically) doesn't exist yet.

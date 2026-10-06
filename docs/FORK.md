# Fork handling: status

> Note (2026-10-06): the PMMR and bitmap mentioned below were replaced by
> one fixed-depth state tree (`state_tree.rs`; see
> `docs/CHAIN_RECURSION.md`). Unwinding a block now restores spent leaves
> and truncates the appended ones; the header carries `state_root` and
> `output_count`.

Progress on item #2 of `BLOCK_TODO.md` ("No fork handling"): side
branches, fork-choice by cumulative work, reorgs, and orphans. All 233
tests pass.

## Done

### Chain work (`pow.rs`)

- `work_for_target(target)` -- Bitcoin's `2^256 / (target + 1)`, computed
  exactly in fixed-width 256-bit arithmetic (`add256`, plus a schoolbook
  `divmod256`), wrapping on overflow the same way Bitcoin's
  `arith_uint256` does.
- Tested against hand-traced values (8 leading zero bits → 256, 16 →
  65536, half-range target → 2) and the two boundary targets (`0` and
  all-`0xff`).

### Undo data and unwinding (`chain.rs`)

- New LMDB databases, all keyed by header hash: `blocks` (full block
  bytes), `block_undo` (`UndoData`), `block_work` (cumulative work),
  `block_retarget` (`RetargetState` after the block), `invalid_blocks`;
  plus `block_heights` (height ‖ hash, for pruning). `storage::MAX_DBS`
  raised from 8 to 16 (12 used).
- `apply_block` split into `apply_block_in_txn`, so several blocks (plus
  unwinds) can share one atomic transaction.
- `UndoData` snapshots, at apply time, the previous tip header, previous
  `current_target` / `window_start_timestamp`, and each spent input's
  `(commitment, position)` -- none of which is recoverable afterwards.
- `unwind_tip` reverses one block: restores spent outputs (bitmap +
  utxo, at their original positions), removes the block's own outputs,
  truncates the PMMR, and restores tip/retargeting state.
- Tests: unwind restores the exact prior state (roots, tip, height,
  target), unwinding to empty, reversing a spend, and restoring
  difficulty across a retarget-window boundary. `bitmap.rs` and
  `utxo.rs` gained tests for the "undo == never having done it"
  property the unwind relies on.

### Fork-choice, reorg, orphans (`chain.rs`)

- `accept_block(block) -> AcceptOutcome`, one of `Applied`,
  `StoredAsSideBranch`, `Reorged { unwound, applied }`, `Orphaned`.
- Side-branch blocks are validated and stored (`store_side_branch_block`)
  in their own transaction, without touching live state. Each is checked
  against *its own branch's* target: the retarget rule is a pure function
  (`RetargetState::after`), and every stored block records the state
  after it, so a fork straddling a retarget-window boundary is handled
  exactly.
- Reorg only on *strictly* more cumulative work. Unwind + replay run in a
  single write transaction; any replay failure aborts it, leaving the
  active chain untouched. This is safe because `Pmmr`, `Bitmap`, and
  `UtxoIndex` hold no in-memory state -- everything lives in LMDB.
- One height cutoff, `reorg_floor` (tip height − `max_reorg_depth`),
  drives three things: blocks at or below it are refused on arrival
  (`Error::ReorgTooDeep`, not stored or pooled); `find_fork_point`
  walks the candidate side back to it (bounded by height, not step
  count, so a branch longer than `max_reorg_depth` can still win if the
  *unwind* is within the limit); and everything strictly below it is
  pruned (`Chain::prune`) after each apply or reorg: side-branch blocks
  entirely, active-chain blocks down to the block itself (undo data,
  work, and retarget state go). Active-chain blocks are kept forever so
  any node can serve a full sync to a new one -- until state-snapshot
  sync backed by the recursive proof exists. An `active_heights` index
  (height → hash) tracks the active chain for that.
  `Chain::open` takes `max_reorg_depth`
  (`main.rs`: 1000; tests: 5).
- In-memory orphan pool, capped at `MAX_ORPHANS` (100), oldest evicted
  first. An orphan is only pooled if its proof of work meets the
  current target made easier by `max_adjustment_factor`
  (`Chain::orphan_target`; `Error::OrphanPowTooWeak` otherwise), so
  flooding the pool costs real work -- a quarter-block each today --
  while a legitimate orphan from just past an easing retarget still
  gets in. This is a heuristic, not consensus: a wrongly refused orphan
  is simply accepted once its parent is known. `accept_block` retries waiting orphans itself, transitively,
  whenever a block connects; orphans' own outcomes aren't reported
  (failures are dropped), but their effect shows in `tip_hash`.
- Invalid-block tracking: a new `invalid_blocks` table. A reorg replay
  that fails on a block-level fault (`Error::is_block_fault`: bad
  validate, lineage, unresolved/duplicate input or output, root
  mismatch -- *not* storage errors or a future timestamp) records the
  failing block and everything after it in that branch. Blocks that
  are, or extend, a recorded block are refused with
  `Error::KnownInvalidBlock`, and a candidate branch containing one is
  rejected before anything is unwound.
- Duplicate detection: a block already stored, or already waiting in
  the orphan pool, returns `AcceptOutcome::AlreadyKnown` and is
  otherwise ignored.
- Tests: reorg aborted by a bad block after good blocks were already
  replayed (active chain unchanged, follow-up block refused without a
  retry); mid-chain fork whose winning branch spends a shared output
  differently (final roots match a node that only saw the winning
  branch); duplicate applied / side-branch / orphan blocks; side-branch
  block valid only under its own branch's post-retarget target; neck-and-
  neck branch replaying `max_reorg_depth + 1` blocks; floor rejection;
  pruning (and a full-depth unwind still working afterwards); orphan
  eviction and automatic connection.

## Gaps / loose ends

1. **A block that fails to apply directly onto the tip isn't recorded
   as invalid** (it was never stored, so nothing can extend it; a
   resend just fails again the same way). Only reorg-replay failures
   are recorded. Intentional.
2. **Orphan pool has no expiry**, only the size cap -- low priority
   now that pooling costs real work.
3. **Far-behind sync refuses orphans**: if the chain eased by more than
   one retarget's swing beyond this node's tip, orphans from there fail
   `orphan_target` and must be re-fetched once their parents arrive.
   Fine for now; real sync should be headers-first, where orphans are
   rare.
4. **`powLimit`** (`BLOCK_TODO.md` #2) -- not started; no longer needed
   for orphan DoS, only for its original purpose (bounding how far
   retargeting can ease difficulty).

# The Bible in the chain

Part of the project's purpose is to carry the Bible: a prophecy archive.
The text is the American King James Version, pinned as `data/akjv.txt.gz`
(1,291,059 bytes; provenance, hashes and license in `data/AKJV.md`).

Storing the text somewhere doesn't make anyone keep it: a node that never
reads it can drop it and still work. So the text is made **load-bearing**
instead, in two ways:

1. **Mining** (proof of work) reads a dataset expanded from the text. Every
   node needs the text to check proof of work, and every miner needs the
   dataset.
2. **Every spend** binds a block of the text into its signature. Every
   wallet needs the text to sign, and every miner to prove.

Neither changes the published proofs: proof size and verification time
stay where they are.

## The text as a consensus constant (`scripture.rs`)

Consensus uses the **compressed bytes as shipped**, never re-compressed,
cut into 32-byte blocks (40,346 of them, the last zero-padded). Gzip makes
the bytes close to random, so none can be predicted rather than stored.
Consensus never needs the decompressed text.

- **`TEXT_ROOT`:** a Poseidon2 Merkle root (16 levels). All 2^16 positions
  are filled, position `i` holding block `i mod 40,346`, so any 16-bit
  index names a block with no range check in a circuit. A block is 11 field
  elements (three bytes each, one-to-one). It's proven with its path: 17
  permutations.
- **Embedded in the binary** (`include_bytes!`): nothing to install or
  configure, and nothing to go missing. Checked against `TEXT_ROOT` at
  startup.
- Reading it needs nothing from consensus: `gunzip -c data/akjv.txt.gz`.

## 1. Memory-bound proof of work (`pow.rs`)

The goal is a proof of work that's **memory-bound, not ASIC-proof**. ASICs
are welcome, but their edge should be better memory (DRAM, HBM, or SRAM),
not more hashing.

### The dataset

`2^items_log` items of 512 bytes (128 field elements), each computed
independently from a text block at a deliberately high cost of `n` = 128
permutations, then squeezed out to 128 elements:

    item[i] = H^128( block[i mod 40,346] ‖ i )

| | Main | Dev |
|---|---|---|
| Dataset | 2^17 items = **64 MiB** (SRAM-feasible for an ASIC) | 2^15 items = 16 MiB |
| Item cost `n` | 128 | 128 |
| Lookups per attempt `k` | 64 | 12 (so the chain step fits dev's 2^17-row recursion) |

- **Recomputing must cost far more than reading**, in energy, since ASICs
  parallelize compute freely. Estimates: a DRAM read is ~5–10 nJ per 64
  bytes, an HBM read ~2–3 nJ, one Poseidon2 permutation on an ASIC ~1–2
  nJ. Recomputing an item costs ~130–260 nJ, so **miners keep the whole
  dataset in memory.**
- **Items are independent**, not a hash chain. A chain would make
  generation sequential, but wouldn't make recomputing harder (an
  attacker could store every m-th item), and validators would need the
  whole dataset.
- **Validators don't need the dataset.** They recompute just the items a
  header touches: ~8,700 permutations, measured at ~16.7 ms on one laptop
  core, and estimated at a few seconds on a microcontroller. They need only
  the text. This keeps validation possible on very low-end hardware.
- **Miners** generate it at startup (~6 s on 12 threads for 64 MiB) and
  keep its Merkle tree (8 MB) to prove chain steps.

### One attempt

    prefix = hash(header without the nonce)        -- once per template
    out    = permute(prefix ‖ nonce ‖ domain)      -- one permutation
    id     = out[0..8]     the block's id (what prev_hash points to)
    mix    = out[8..24]    16 elements
    64 times:
        j      = (Σ mix) mod 2^items_log           (canonical value)
        acc[e] = Σ_c item[j][16c + e] · mix[(e + c) mod 16]
        t[e]   = acc[e] + mix[e]
        mix[e] = t[e] · t[e + 1] + K[e]
    pow = hash(id ‖ mix)  ≤  target

- **Midstate:** the header is hashed once per template, so an attempt
  costs one permutation to start and two to finish.
- **Every element of every item counts,** each multiplied by a weight that
  depends on the mix, so the weights change every attempt and items can't
  be precompressed (by storing column sums, say).
- **Each index depends on the previous read,** so reads can't be prefetched
  or skipped. Miners can only overlap separate attempts, which makes mining
  bound by memory bandwidth.
- **The 128 products per lookup are independent,** so they vectorize. The
  only sequential step is the 16-element nonlinear update.

**Measured** on a Ryzen 5 7530U (6 cores, 16 MB L3, AVX2), against the
real 64 MiB dataset: ~295,000 attempts/s on 12 threads, reading ~9.7
GB/s. A dataset that fits in cache runs ~1.6× faster, so memory is ~40%
of a CPU miner's time with today's code. The rest is arithmetic, half of
it the two Poseidon2 permutations per attempt. Hand-written AVX2 folding
and SIMD Poseidon2 (miner-side only, no consensus change) should make a
CPU clearly memory-bound. On an ASIC, where arithmetic is nearly free,
memory is ~98%+ of the energy.

**On energy:** in equilibrium, miners spend roughly up to the value of
the reward, whatever the algorithm. A memory-bound design shifts that
spending from electricity toward hardware (memory capacity and
bandwidth), so the same security budget burns less energy. It's a ratio,
not "low energy" in absolute terms.

### In the chain step (`chain_step.rs`)

The chain step proves each header's id and proof of work:
- the prefix over the header's bytes, and the attempt permutation;
- each lookup's index from a **canonical** 31-bit decomposition of the
  mix's sum (otherwise a prover could pick a different index than
  validators);
- each 512-byte item proven against the dataset tree's root, which is
  built into the step's key, so it's not a separate consensus constant;
- the same folding, then the final hash compared with the target.

Measured: **85,324 rows on main**, taking the chain step to ~430k of its
524k rows (82%). Dev's recursion is 2^17 rows, so dev uses 12 lookups
(~15k rows) instead of 64.

## 2. Every spend binds a text block (`wots.rs`, `block_air.rs`)

Each input's WOTS signature binds the text block its own randomizer
selects:

    position = compress(param ‖ TAG_SELECT ‖ message ‖ randomizer)[0] mod 2^16
    bound    = compress(TAG_BIND ‖ message ‖ block[position mod 40,346])
    digits   = derive_digits(param, bound, randomizer)   -- as before, on `bound`

The signer re-rolls the randomizer until the digits hit the target sum,
and each try selects a different block, so **signing takes the whole
text.** Native verification needs it too.

In the chunk circuit, each input's section gains 19 blocks (one
permutation each):
- `SEL`: the selection, decomposed like `DIG`'s digits;
- `TLEAF`: the block's leaf;
- 16 × `TNODE`: the path up to `TEXT_ROOT`;
- `BIND`: the binding.

They're wired over the bus: `DIG` sends its randomizer to `SEL` and
receives `bound` from `BIND`; `SEL` sends the position's bits to the path;
`TLEAF` sends the block to `BIND`. That's about +7% of an input's
permutations, and 4 more columns (231). A full chunk still fits its 4,096
blocks. Chunk proofs aren't published, so **published proofs don't
change.**

## Steps

1. **Text commitment** (done): embedded file, `TEXT_ROOT`, startup check.
2. **Proof of work, natively** (done): dataset, attempt, midstate, mining
   fast path, parameters in `DifficultyConfig` (tests use tiny ones).
3. **Proof of work in the chain step** (done): measured, and a real
   recursive chain proved on dev.
4. **Signatures bind a block** (done): native and chunk circuit.
5. **Switch-over:** genesis re-mined on both networks (the block id
   changed), tree and chain keys regenerated, wire version 9, real-proof
   tests and a live dev network.

Not done (miner-side, no consensus change): multi-threaded mining in the
node, AVX2 folding, SIMD Poseidon2.

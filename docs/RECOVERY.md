# Wallet recovery from the mnemonic alone

Goal: a user who has lost everything but their 24 backup words can run a
node, type the words, and get back every unspent output -- with correct
amounts, maturity and spent status -- and keep using the wallet without
ever reusing a one-time key.

## The problem

An output on chain is only a commitment:

```text
commitment = H(DOMAIN_COMMITMENT, pubkey_hash ‖ amount_limbs)
```

From the seed a wallet can re-derive every `pubkey_hash`
(`keychain::derive(KeyId { account, index })`), but to recognise its
output on chain it would also need the exact `amount` -- a u64 the sender
chose (or, for a mining reward, `REWARD + fees`). That can't be searched.
So today the wallet's LMDB file *is* the funds: the seed alone recovers
nothing.

## The fix: a recovery nonce on every output (Grin-style)

Grin solves the same problem by letting the owner "rewind" a range proof
to read back the amount. We have no range proof, so each output carries
the equivalent explicitly: **16 bytes, readable only with the owner's
view key**.

### View key

```text
view_key = hash_bytes_32("tabernacle-view-v1" ‖ seed)
```

Derived from the seed, separate from every spending key. It can find and
read the wallet's outputs but can't spend them (spending needs the WOTS
secret keys, derived from the seed by a different domain). Whoever holds
it sees the wallet's incoming outputs and amounts -- useful for
view-only/audit wallets, but a secret to protect.

### The 16-byte nonce

```text
plaintext (16 B) = index (u32 LE) ‖ amount (u64 LE) ‖ magic (u32, "TBN1")
pad       (16 B) = hash_bytes_32("tabernacle-recovery-v1" ‖ view_key ‖ commitment)[..16]
nonce     (16 B) = plaintext XOR pad
```

- **The commitment is the nonce's nonce**: it's unique per output (fresh
  one-time key; consensus refuses a duplicate live output), so no pad is
  ever reused.
- **`magic`** lets a scan discard outputs that aren't ours with one hash
  each (a false match has probability 2^-32, and is then caught by the
  next check).
- **Confirmation**: a decrypted `(index, amount)` is ours only if
  `keychain.output(KeyId(ACCOUNT, index), amount).commitment()` equals
  the commitment. False positives are impossible past this point.
- The account isn't stored: the wallet uses one (`ACCOUNT`); a future
  multi-account wallet can spend the top bits of `index` or the magic.

**Mandatory and fixed-size.** Every output carries exactly 16 bytes,
including outputs from wallets that don't care about recovery (they can
fill it with random bytes). An optional or variable field would mark
which outputs came from which software -- a privacy leak.

### Who writes it

Whoever chooses the output's key:

| output | written by |
|---|---|
| payment (slate S2) | the **receiver**, in `Wallet::receive` |
| change | the sender's wallet, in `send` / `self_transfer` |
| mining reward | the miner's wallet, in `reward_output` |

**Once a transaction is signed, nobody can alter a nonce** (done; see
"Binding" below): the signing message covers every output's nonce, and
a block's proof ties the nonces the block publishes to the signed ones.
The one party who could still change one is the **sender of a slate
payment, before signing** -- the receiver writes its nonce into S2, and
the sender signs the final transaction. That can't touch the funds,
only that output's recoverability; the receiver's wallet checks, when
its output confirms, that the on-chain nonce opens to what it wrote, and
warns (keep the wallet file until it's spent) if not.

### Binding (done)

Putting the nonce *inside* the commitment would be circular -- the
nonce's pad is derived from the commitment, which is what lets a scan
read it from public data alone -- and would cost a public random part
(56-byte outputs), two permutations per commitment, and nonces on every
input. Instead:

- **The signing message covers it.** The message is laid out one item
  per sponge block: the input count, each input's commitment (and
  zeros), then each output's commitment and its nonce as eight 16-bit
  limbs (`output::nonce_limbs`). Altering a nonce after signing breaks
  the signature.
- **The proof's statement covers it.** Each output's public tuple is
  `[TAG_POUT, 0, 0, commitment, nonce]`; the circuit's `COUT` blocks
  carry the nonce (`NONCE` columns) and send commitment and nonce in one
  bus tuple both to the public side and to their transaction's message
  sponge -- one tuple, so a prover can't pair nonces with different
  outputs. `Proof::verify(inputs, outputs, nonces)` checks the block
  body's nonces; a miner can't publish different ones.

No on-chain size change, commitments and inputs unchanged; the
circuit's trace is 8 columns wider and tuples grow from 11 to 19
elements.

### Cost

Outputs grow from 32 to 48 bytes on chain; inputs stay 32. For a typical
block (about two outputs per input) that's roughly +30%, still far below
any design that stores signatures. The proof is unchanged: the nonce is
not part of the circuit.

## Recovery procedure

1. **Mnemonic → seed.** 24 BIP39 English words ↔ the 32-byte keychain
   seed (256 bits of entropy, 8-bit checksum). The seed *is* the entropy
   -- no PBKDF2 stretching, so words and seed map one-to-one. (A BIP39
   passphrase can be added later as an option.)
2. **Seed → view key** (above).
3. **Scan every output of the active chain** -- spent ones too (see
   "Choosing the next key index"). For each `(commitment, nonce)`:
   decrypt, check `magic`, confirm by recomputing the commitment. Cost:
   one hash per output ever created, plus one key derivation per actual
   match; independent of how many keys the wallet used (no gap limit).
4. **Rebuild the wallet**: each match becomes an `OwnedOutput` with
   `origin: Recovered`, `seen_height` = its block's height (so coinbase
   maturity is right), `spent` = not in the UTXO set.
5. **Choosing the next key index**: `next_index = max(matched index) +
   RECOVERY_INDEX_MARGIN` (e.g. 1000). Indices only grow, and every key
   that ever *signed* spent an output that's on chain -- so the maximum
   over *all* outputs (spent included) bounds every signing key. The
   margin covers keys handed out but never confirmed (unanswered slates,
   rewards for blocks someone else won), which never signed but needn't
   be reused either.

### Hazards

- **A signed transaction in flight.** If the wallet was lost after
  signing a spend that hasn't confirmed yet, the recovered wallet sees
  that output as unspent -- and signing a *different* spend of it would
  publish a second WOTS signature, leaking the key. So recovered outputs
  start as **unconfirmed-safe**: the wallet first checks the mempool for
  a transaction spending them (and marks them `Signed` if found), and
  refuses to spend a recovered output until `RECOVERY_HOLD_BLOCKS` (e.g.
  10) blocks have passed without such a transaction appearing.
- **Two wallets from the same seed at once** can hand out the same index
  -- and sign twice. Recovery must be the only live copy; the CLI says so.
- **A nonce altered by a dishonest sender before signing** (see "Who
  writes it"): that output is invisible to recovery; the warning at
  confirmation time is the defence. After signing, alteration is
  impossible.
- Recovery needs the full active chain's outputs. The pruning policy keeps
  every active-chain block, so this holds.

## Steps

### 1. Mnemonic (`mnemonic.rs`, done)
Done: `mnemonic.rs`.
- [x] BIP39 English wordlist (2048 words, embedded as
      `src/bip39_english.txt`; a test checks it against the list's
      published SHA-256).
- [x] `seed ↔ words` (24 words, SHA-256 checksum per BIP39, SHA-256
      implemented locally), round trips and the BIP39 test vectors;
      rejects wrong length, unknown words, bad checksum. Accepts any case
      and spacing, and four-letter prefixes (unique in the list).
- [x] `Keychain::{phrase, from_phrase}`; CLI: `seed` shows the numbered
      words (with a warning) instead of hex.

### 2. View key and nonce (`recovery.rs`, done)
- [x] `Keychain::view_key()` -> `recovery::ViewKey` (zeroed on drop,
      never printed).
- [x] `recovery::seal(view_key, commitment, index, amount) -> [u8; 16]`,
      `open(view_key, commitment, nonce) -> Option<(index, amount)>`,
      and `identify(keychain, view_key, account, commitment, nonce) ->
      Option<(KeyId, amount)>` (opens, then confirms by recomputing the
      commitment); `random_nonce()` as filler. Tests: round trip; wrong
      view key, wrong commitment, wrong account and every single flipped
      bit fail; equal contents seal to unrelated bytes; strangers'
      outputs and random filler are never identified as ours.

### 3. Outputs carry the nonce (consensus; done)
- [x] `Output` gains `nonce: [u8; 16]` (`Output::new` gives zeros,
      `with_nonce` sets it); the transaction encoding carries it
      (encoding version 2, 56 bytes per output) and the transaction id
      covers it. (At first the signing message didn't, so anyone handling
      a transaction could alter a nonce; the signature and the proof now
      cover it -- see "Binding", encoding version 3.)
- [x] Block body: `nonces: Vec<[u8; 16]>`, parallel to the sorted
      `outputs` (`nonces[i]` belongs to `outputs[i]`); encoded after the
      outputs; `Block::validate` requires exactly one per output.
      `body_hash` now starts with a body-format version (2) and hashes
      each list's length (which also fixes an old ambiguity: a commitment
      moved between the input and output lists used to hash the same).
- [x] Block builder copies nonces from the transactions
      (`BlockBody::add_transaction`).
- [x] Chain: a new `output_index` database -- commitment -> height ‖
      nonce for every output the active chain created, written on apply,
      removed only on unwind (spending leaves it, since recovery needs
      spent outputs). `Chain::output_record(commitment)` and
      `Chain::for_each_output(f(record, unspent))`.
- [x] Format breaks, made explicit: wire version 5, slate version 2,
      transaction encoding version 2, and a re-mined genesis block (its
      body hash changed), so data from before refuses to open with
      "different genesis block -- delete it, or use another --data-dir".
- [x] Size: outputs are 48 bytes in a block (commitment + nonce); the
      2 MB cap holds ~43k outputs with no inputs.

### 4. Wallet writes and checks nonces (done)
- [x] Every output the wallet creates is sealed (`Wallet::sealed_output`):
      rewards, change, self-transfers, and the receiver's output in a
      slate.
- [x] Slates carry the receiver's nonce -- they hold whole `Output`s, so
      it travels with no further change (slate version 2).
- [x] On confirmation, `refresh` reads the output's on-chain nonce
      (`ChainView::output_record`, backed by the chain's output index)
      and checks it identifies the output; it returns any that don't, and
      the node logs a warning ("keep this wallet's files until it's
      spent").
- [x] Bonus from the output index: an output's confirmations now count
      from the block that created it, not from when the wallet first
      noticed it -- so a wallet that was offline sees maturity correctly.
- [x] Tests: every kind of output (reward, change, received, the pieces
      of a self-transfer) opens with its owner's seed; an altered nonce is
      reported once at confirmation; confirmation height after downtime;
      both end-to-end chain tests assert every nonce arrived intact.

### 5. Recovery (done)
- [x] `Wallet::restore(dir, keychain)` -- refuses a directory that holds
      a wallet; creates one in a **recovering** state that hands out no
      keys (no mining, sending or receiving): any key handed out before
      the chain has caught up might be one the lost wallet already used.
- [x] `Wallet::finish_recovery(chain)` -- one scan of the chain's output
      index (`ChainView::for_each_output`); each output that
      `recovery::identify` confirms is recorded (`Origin::Recovered`,
      true height, spent or not); key handout resumes at
      `max index + 1 + RECOVERY_INDEX_MARGIN` (1000). Unspent recovered
      outputs are `Lock::Held` until `RECOVERY_HOLD_BLOCKS` (10) blocks
      after recovery, and get a reward's maturity (we can't tell whether
      one was a reward).
- [x] In-flight spends: `Wallet::observe_spend(tx)` -- every transaction
      the node's mempool accepts that spends an output of ours we didn't
      sign marks it signed away and keeps the transaction (resubmitted at
      startup like our own). With the hold, a restored wallet never signs
      a second spend of an output the lost wallet had already signed.
- [x] `refresh`: an output the chain created that's no longer unspent is
      **spent** (by anyone holding our keys), not vanished -- before, only
      spends we signed ourselves were recognized.
- [x] "Caught up": the network thread shares the highest tip any peer
      has reported (`net::Node::peer_height`, from `transfer`); the node
      scans once its chain reaches it -- or at once, with no peer heights
      when started `--standalone` (a standalone node is its network).
- [x] Startup: `--recover` reads the 24 words from stdin (asks again on
      a mistake), then runs as normal; `status` shows the recovery's
      progress, and the log reports what was found.
- [x] Tests: a wallet that mined, paid, received, split and made change
      is lost and restored from its words alone -- the same unspent
      outputs, spent ones known, no key reuse, held then spendable, and
      it spends; an in-flight spend is respected and resubmitted;
      restoring over an existing wallet is refused; an output spent by a
      copy of the wallet reads as spent.
- [x] Live, over the network (2026-10-05): Alice mined 14 blocks and paid
      Bob 0.25; she was shut down; Carol -- a new node with an empty data
      directory, knowing only Bob, started with `--recover` and Alice's
      words -- synced 14 blocks, scanned, and found all 15 of Alice's
      outputs (14 unspent, 13.75 in all -- exactly Alice's total, every
      output's amount, height and commitment matching; the spent reward
      known as spent; Bob's output not claimed), new keys from index 1015.

### 6. Proving it works (done)
- [x] Unit: seal/open; a scan finds exactly our outputs among others';
      `next_index` is above every used index; holds; in-flight spends.
- [x] **Acceptance** (`e2e::a_wallet_restored_from_its_words_alone_with_real_proofs`,
      release, ~1.5 minutes): real proofs on a chain that checks every
      one. Alice mines 11 blocks, pays Bob, is paid by Bob, splits a coin,
      and has one more spend signed and in the mempool when her wallet is
      deleted. A wallet restored from her **24 words alone**:
      - finds exactly her 17 unspent outputs (13.8001 coins), and the 2
        spent ones;
      - resumes keys at 1019 -- past every key she ever handed out (20,
        including the in-flight spend's outputs, not yet on chain);
      - holds everything for 10 blocks; marks the in-flight spend's input
        as signed away (re-signing it is refused) and resubmits it;
      - once that spend confirms, owns its outputs (found through the
        spend itself, by their nonces);
      - after the hold, pays Bob from new keys only, and Bob receives it.
- [x] Live over the network (see step 5).
- [x] Display: recovered outputs show as `held` (`balance`: "held ...
      spendable from height N"; `outputs`: "held to N") rather than as
      immature rewards.

## Later (not needed for recovery)

- [x] Make the nonce tamper-proof -- done through the signature and the
      proof's statement rather than the commitment (see "Binding").
- [x] Passphrase (done): `mnemonic::seed_from(entropy, passphrase)` --
      no passphrase keeps seed = entropy; with one, PBKDF2-HMAC-SHA256
      (100,000 rounds, salt `"tabernacle-passphrase-v1" ‖ entropy`).
      SHA-256, HMAC and PBKDF2 are implemented locally and checked
      against published vectors. The wallet stores the words' entropy
      and whether a passphrase was used; `seed` shows the words and says
      when the passphrase is also needed. `--passphrase` protects a new
      wallet (asked twice) or, with `--recover`, reads it. A wrong
      passphrase restores an empty wallet, as in BIP39.
- View-only wallets (view key without the seed): needs the public keys
  to confirm matches, which hash-based keys can't derive without the
  seed -- a view-only wallet would trust `magic` alone.

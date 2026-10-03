//! Chain-state-dependent block validation: resolving a block's inputs
//! and outputs against the real `Pmmr`/`Bitmap`/`UtxoIndex`, checking
//! balance and double-spends (both only knowable once those lookups
//! happen), applying the resulting updates, and checking the header's
//! claimed roots match what applying the block actually produced --
//! everything `block::Block` deliberately doesn't do on its own, since
//! it has no access to (or need for) any chain state.
//!
//! **Placeholder.** Deferred while `block.rs` gets more work first; not
//! implemented yet.

#![allow(dead_code)]

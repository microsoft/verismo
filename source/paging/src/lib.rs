//! A page table whose safety properties are proved, and whose concurrency is
//! finer than one lock per tree.
//!
//! # What the crate provides
//!
//! [`handle::GenericPageTable`] owns a tree and offers the operations an OS
//! needs: `walk` and `translate` walk it, `map`, `unmap` and `protect` change
//! one address, `map_range`, `unmap_range` and `protect_range` change a whole
//! range in one pass -- splitting a larger mapping when, and only when, the
//! range ends inside one -- `install_self_map` makes the tables visible to
//! themselves, and `free` takes the tree apart.
//!
//! # Two levels of exclusion
//!
//! The *outer* level guards the shape of the tree and is Rust's: an operation
//! that only reads or grows the tree takes `&self`, and `free`, which reclaims
//! pages a walker could be standing in, consumes the handle. The *inner* level
//! is one lock per table page, supplied by the OS
//! ([`os_contract::PageLock`]), and it is the only lock a map or an unmap
//! takes -- two threads updating different pages never contend. A walk takes
//! neither: slots are read through `concurrent_rw`, which makes a reader's
//! view of a slot imprecise but never wrong.
//!
//! # Ghost state instead of type state
//!
//! A page's level, and whether the tree is installed in hardware, are *tracked
//! ghost state* rather than type parameters. One `descend`, one `map_at`, one
//! `range_at` serve every level, so there is no macro-generated family of
//! per-level functions and no `Active`/`Inactive` duplication of the API.
//!
//! # Where the tokens of a page live
//!
//! A table page is `PTPage::count` slots under the `concurrent_rw` protocol.
//! Its *readers* are escrowed in the entry that points at it, so a walker that
//! reads a table entry gets the child's readers with it and may descend on a
//! `&` borrow alone; its *writers* are deposited in the page's own lock, so a
//! thread that has walked to a page can lock it knowing only a pointer to it.
//! Hardware bits cannot say which entries escrow a page -- at the leaf level
//! "present and not huge" means a 4 KiB mapping -- so an ignored software bit
//! marks them; see `structs::arch_contract::GenericPageTableFlagsSpec`.
//!
//! # How a page is named
//!
//! Every operation names the page it works on by a `*mut PTPage<A>`, built
//! from that page's own tokens, so the pointer's provenance is the provenance
//! the tokens were made with and the entry at an index is a pointer
//! computation rather than an address arithmetic the type system knows
//! nothing about. `structs::ptpage` is where a pointer is made and where a
//! slot's word is found.
//!
//! # What is proved, and what is not
//!
//! Proved: every access to a table page goes through a token that says the
//! page is there and that the accessor is allowed to touch it; a slot is
//! written only under that page's lock; a table pointer, once stored, keeps
//! pointing at the same page at the same level, which is what makes descending
//! on a stale read sound; a page's frames are never handed back while anything
//! can still reach them; and a caller cannot forget a TLB invalidation, because
//! the operations that need one return a value that must be used.
//!
//! Not proved: that a mapping installed by `map` is the one `translate` finds
//! afterwards. Nothing here says so, and under this locking discipline nothing
//! could without a tree-wide invariant: the moment an operation drops a page's
//! lock, another thread may change what it just wrote. The specifications
//! therefore describe what an operation does to the slot *while it holds the
//! writer*, and stop there.
//!
//! Also not proved: that a page's ghost level matches its depth in the tree.
//! Recursion is bounded by the level it is passed instead. Stating it would
//! need a slot to expose, in specification, the payload it escrows, which
//! `concurrent_rw` deliberately keeps inside its invariant.
//!
//! # What an embedder owes
//!
//! Everything OS-specific is in [`os_contract`]: allocation, the direct map,
//! the per-page lock, and TLB invalidation. Everything architecture-specific
//! is in [`ArchPagingMeta`] and its flag traits; `arch::x86_64::paging`
//! discharges both for four-level x86_64 paging.
#![no_std]
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]
#![cfg_attr(verus_only, verifier::allow(unknown_automatic_derive))]
#![cfg_attr(verus_only, allow(macro_expanded_macro_exports_accessed_by_absolute_paths))]
#![allow(unused_braces)]

use builtin_macros::*;

mod arch;
mod proofs;
pub mod specs;
mod structs;
pub mod util;

#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::reg_contract::{
    cr0_paging_precondition, cr3_paging_precondition, cr4_paging_precondition,
    efer_paging_precondition, efer_value, low_bits_mask_u64, paging_inv, PagingRegisters, MSR_EFER,
};
pub use proofs::address_space::UniqueAddress;
pub use structs::address;
pub use structs::arch_contract::{ArchPagingGeometry, ArchPagingMeta, GenericPageTableFlags};
pub use structs::concurrent_pt;
pub use structs::entry;
pub use structs::frame;
pub use structs::free;
pub use structs::handle;
pub use structs::level;
pub use structs::map;
pub use structs::os_contract;
pub use structs::page;
pub use structs::ptpage;
pub use structs::range;
pub use structs::region;
pub use structs::sizes;
pub use structs::split;
pub use structs::state;
pub use structs::tlb;
pub use structs::unmap;
pub use structs::walk;

verus! {

global size_of usize == 8;

} // verus!

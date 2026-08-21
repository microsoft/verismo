//! What an embedder owes the page table.
//!
//! The page table allocates no memory, takes no lock and knows no virtual
//! memory layout of its own: each of those is a service the host supplies, and
//! this trait is where the corresponding proof obligations are concentrated.
//! One verified page table can then be embedded in several systems, each
//! discharging these obligations in its own verification, which is the same
//! shape as the register contract in `arch::x86_64::reg_contract`.
//!
//! The per-page lock is the LOCK invariant of `doc/page-table.md`: writers of
//! one table page serialize on it. The page table never sees the lock itself,
//! only the writer tokens it hands out and the `Deposit` receipt naming which
//! page they belong to.
use vstd::prelude::*;
use vstd::resource::Loc;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::level::PagingLevel;
use crate::structs::table::{ChildOf, TableWriters};

verus! {

/// The half of the host contract that mentions no page-table token: where a
/// frame is mapped, and what a lock receipt says about the page it guards.
///
/// Split out of [`PagingHost`] for the same reason `ArchPagingGeometry` is
/// split out of `ArchPagingMeta`, and for one more: what a table slot escrows
/// is defined against this trait, while `PagingHost`'s own methods are defined
/// against the escrow. Keeping the token-carrying methods out of here is what
/// keeps those two definitions from being mutually recursive.
pub trait PagingHostAddr: 'static + Sized {
    /// Receipt that the host's lock for one table page holds the writer half of
    /// that page's slots. A walker carries it to name the lock it must take
    /// before touching a slot; it says nothing about the slot values.
    type Deposit;

    spec fn deposit_page(deposit: Self::Deposit) -> usize;

    spec fn deposit_slot_ids(deposit: Self::Deposit) -> Map<int, Loc>;

    spec fn spec_paddr_to_vaddr(paddr: usize) -> usize;

    /// Where the host has mapped a page-table frame. `paddr` is always clean —
    /// callers strip the architecture's confidentiality tags first.
    fn paddr_to_vaddr(paddr: PhysAddr) -> (ret: VirtAddr)
        ensures
            ret@ == Self::spec_paddr_to_vaddr(paddr@),
    ;
}

/// The services the page table calls into: the per-page lock, in the form of
/// checking the writer half of a page's slots in and out.
pub trait PagingHost: PagingHostAddr {

    /// Takes this page's lock and hands back the writer half of its slots.
    ///
    /// The `Deposit` is what addresses the lock: a caller cannot ask for the
    /// writers of a page it holds no receipt for.
    fn lock_page<A: ArchPagingMeta, L: PagingLevel + ChildOf<A, Self>>(
        &self,
        base: VirtAddr,
        Tracked(deposit): Tracked<&Self::Deposit>,
    ) -> (ret: Tracked<TableWriters<A, Self, L>>)
        requires
            Self::deposit_page(*deposit) == base@,
        ensures
            ret@.wf(),
            ret@.base == base@,
            ret@.ids == Self::deposit_slot_ids(*deposit),
        opens_invariants none
    ;

    /// Returns the writer half and releases the lock.
    fn unlock_page<A: ArchPagingMeta, L: PagingLevel + ChildOf<A, Self>>(
        &self,
        base: VirtAddr,
        Tracked(writers): Tracked<TableWriters<A, Self, L>>,
        Tracked(deposit): Tracked<&Self::Deposit>,
    )
        requires
            writers.wf(),
            writers.base == base@,
            Self::deposit_page(*deposit) == base@,
            writers.ids == Self::deposit_slot_ids(*deposit),
        opens_invariants none
    ;

    /// Puts a freshly built page's writers into the host's custody, so that
    /// later updates of that page can lock it. This is the last step of
    /// PUBLISH: after it, the page is reachable by other walkers, and its
    /// writers are reachable only through the lock.
    fn deposit_writers<A: ArchPagingMeta, L: PagingLevel + ChildOf<A, Self>>(
        &self,
        base: VirtAddr,
        Tracked(writers): Tracked<TableWriters<A, Self, L>>,
    ) -> (ret: Tracked<Self::Deposit>)
        requires
            writers.wf(),
            writers.base == base@,
        ensures
            Self::deposit_page(ret@) == base@,
            Self::deposit_slot_ids(ret@) == writers.ids,
        opens_invariants none
    ;
}

} // verus!

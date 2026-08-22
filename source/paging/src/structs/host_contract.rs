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
use crate::structs::table::TableWriters;

verus! {

pub trait PagingHost: 'static + Sized {
    /// Receipt that the host's lock for one table page holds the writer half of
    /// that page's slots. A walker carries it to name the lock it must take
    /// before touching a slot; it says nothing about the slot values.
    type Deposit;

    spec fn deposit_page(deposit: Self::Deposit) -> usize;

    spec fn deposit_slot_ids(deposit: Self::Deposit) -> Seq<Loc>;

    spec fn spec_paddr_to_vaddr(paddr: usize) -> usize;

    /// Where the host has mapped a page-table frame. `paddr` is always clean —
    /// callers strip the architecture's confidentiality tags first.
    fn paddr_to_vaddr(paddr: PhysAddr) -> (ret: VirtAddr)
        ensures
            ret@ == Self::spec_paddr_to_vaddr(paddr@),
    ;

    /// Takes this page's lock and hands back the writer half of its slots.
    ///
    /// The `Deposit` is what addresses the lock: a caller cannot ask for the
    /// writers of a page it holds no receipt for.
    fn lock_page<A: ArchPagingMeta>(
        &self,
        base: VirtAddr,
        Tracked(deposit): Tracked<&Self::Deposit>,
    ) -> (ret: Tracked<TableWriters<A>>)
        requires
            Self::deposit_page(*deposit) == base@,
        ensures
            ret@.ids() =~= Self::deposit_slot_ids(*deposit),
        opens_invariants none
    ;

    /// Returns the writer half and releases the lock.
    fn unlock_page<A: ArchPagingMeta>(
        &self,
        base: VirtAddr,
        Tracked(writers): Tracked<TableWriters<A>>,
        Tracked(deposit): Tracked<&Self::Deposit>,
    )
        requires
            Self::deposit_page(*deposit) == base@,
            writers.ids() =~= Self::deposit_slot_ids(*deposit),
        opens_invariants none
    ;

    /// Puts a freshly built page's writers into the host's custody, so that
    /// later updates of that page can lock it. This is the last step of
    /// PUBLISH: after it, the page is reachable by other walkers, and its
    /// writers are reachable only through the lock.
    fn deposit_writers<A: ArchPagingMeta>(
        &self,
        base: VirtAddr,
        Tracked(writers): Tracked<TableWriters<A>>,
    ) -> (ret: Tracked<Self::Deposit>)
        ensures
            Self::deposit_page(ret@) == base@,
            Self::deposit_slot_ids(ret@) =~= writers.ids(),
        opens_invariants none
    ;
}

} // verus!

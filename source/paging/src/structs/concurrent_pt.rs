//! The tracked state of a page table: what owning a table page means, and what
//! a slot promises to a reader that is walking without a lock.
//!
//! A slot is one aligned machine word shared between the hardware walker, any
//! number of software walkers, and one writer at a time. That is exactly the
//! multiple-reader/single-writer setting `concurrent_rw` models, so the entry
//! itself is the protocol's value type: `RWShared` is what a walk carries and
//! `WritePerm` is what an update carries.
//!
//! How an entry behaves under that protocol -- what its payload is and where a
//! slot's value may go -- is in `specs::concurrent_entry`.
use concurrent_rw::{RWShared, WritePerm};
use vstd::prelude::*;
use vstd::raw_ptr::IsExposed;
use vstd::resource::Loc;

use crate::structs::arch_contract::{entries_per_table, slot_addr, ArchPagingMeta};
use crate::structs::entry::PageTableEntry;

verus! {

/// The reader half of one table page: one shared token per entry, plus what a
/// walk needs to turn an entry's frame back into a pointer.
///
/// This is also a slot's payload, which is what makes it self-referential: the
/// tokens of a page at depth `d` are escrowed in the entry at depth `d + 1`
/// that points at it.
pub struct PTPageSharedPerm<A: ArchPagingMeta> {
    pub slots: Seq<RWShared<PageTableEntry<A>, PTPageSharedPerm<A>>>,
    pub provenance: IsExposed,
    pub base: usize,
    pub frame: usize,
    pub depth: usize,
}

impl<A: ArchPagingMeta> PTPageSharedPerm<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: RWShared<PageTableEntry<A>, PTPageSharedPerm<A>>| slot.id())
    }

    /// Every entry of the page is owned, and entry `index` is the token for the
    /// word the architecture puts at that index.
    pub open spec fn wf(self) -> bool {
        &&& self.slots.len() == entries_per_table::<A>()
        &&& forall|index: int|
            0 <= index < self.slots.len() ==> {
                &&& (#[trigger] self.slots[index]).ptr()@.addr == slot_addr::<A>(self.base, index)
                &&& self.slots[index].ptr()@.provenance == self.provenance@
            }
    }
}

/// The writer half of the same page, matched to the reader half entry by entry.
///
/// A host lock hands this out; holding it is what makes an update the only
/// writer of those slots.
pub struct PTPageWritePerm<A: ArchPagingMeta> {
    pub slots: Seq<WritePerm<PageTableEntry<A>>>,
}

impl<A: ArchPagingMeta> PTPageWritePerm<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: WritePerm<PageTableEntry<A>>| slot.id())
    }
}

} // verus!

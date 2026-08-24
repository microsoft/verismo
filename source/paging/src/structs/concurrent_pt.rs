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
use concurrent_rw::WritePerm;
use vstd::prelude::*;
use vstd::raw_ptr::IsExposed;
use vstd::resource::Loc;

use crate::structs::arch_contract::{slot_addr, ArchPagingMeta};
use crate::structs::entry::PTEntry;
use crate::structs::ptpage::PTPage;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::SlotShared;

verus! {

/// The reader half of one table page: one shared token per entry, plus what a
/// walk needs to turn an entry's frame back into a pointer.
///
/// This is also a slot's payload, which is what makes it self-referential: the
/// tokens of a page at level `l` are escrowed in the entry of the level `l + 1`
/// page that points at it. The level is ghost state rather than a type
/// parameter, so one walk serves every level.
pub tracked struct PTPageSharedPerm<A: ArchPagingMeta> {
    pub tracked slots: Seq<SlotShared<A>>,
    pub tracked provenance: IsExposed,
    pub ghost base: usize,
    pub ghost level: PageLevel,
}

impl<A: ArchPagingMeta> PTPageSharedPerm<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: SlotShared<A>| slot.id())
    }

    /// Every entry of the page is owned, and entry `index` is the token for the
    /// word the architecture puts at that index of the page at `base`.
    ///
    /// Which physical frame that is, is not stated here: a page is named by
    /// where it is readable, which is what a walker computes and what it gives
    /// the OS when it asks for the page's lock. The correspondence to a frame
    /// belongs to the entry that points at the page -- see
    /// `PTEntry::wf_payload`.
    pub open spec fn wf(self) -> bool {
        &&& self.slots.len() == PTPage::<A>::count()
        &&& forall|index: int|
            0 <= index < self.slots.len() ==> {
                &&& (#[trigger] self.slots[index]).location()@.addr == slot_addr::<A>(self.base, index)
                &&& self.slots[index].location()@.provenance == self.provenance@
            }
    }
}

/// Matching ids is matching slots: the readers and writers of a page line up
/// entry by entry, which is what lets an update take the writer of the slot it
/// walked to.
pub proof fn lemma_ids_match<A: ArchPagingMeta>(
    writers: PTPageWritePerm<A>,
    page: PTPageSharedPerm<A>,
)
    requires
        writers.ids() =~= page.ids(),
    ensures
        writers.slots.len() == page.slots.len(),
        forall|index: int|
            0 <= index < writers.slots.len() ==> (#[trigger] writers.slots[index]).id()
                == page.slots[index].id(),
{
    assert(writers.ids().len() == writers.slots.len());
    assert(page.ids().len() == page.slots.len());
    assert forall|index: int| 0 <= index < writers.slots.len() implies (
    #[trigger] writers.slots[index]).id() == page.slots[index].id() by {
        assert(writers.ids()[index] == page.ids()[index]);
    }
}

/// The writer half of the same page, matched to the reader half entry by entry.
///
/// A host lock hands this out; holding it is what makes an update the only
/// writer of those slots.
pub tracked struct PTPageWritePerm<A: ArchPagingMeta> {
    pub tracked slots: Seq<WritePerm<PTEntry<A>>>,
}

impl<A: ArchPagingMeta> PTPageWritePerm<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: WritePerm<PTEntry<A>>| slot.id())
    }
}

} // verus!

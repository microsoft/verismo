//! The tracked state of a page table: what owning a table page means, and what
//! a slot promises to a reader that is walking without a lock.
//!
//! A slot is one aligned machine word shared between the hardware walker, any
//! number of software walkers, and one writer at a time. That is exactly the
//! multiple-reader/single-writer setting `concurrent_rw` models, so the entry
//! itself is the protocol's value type: `RWShared` is what a walk carries and
//! `WritePerm` is what an update carries.
//!
//! A table entry's payload *is* the child page it points at, so publishing an
//! entry publishes the child's reader tokens with it and a walker may descend
//! on a `&` borrow alone. `entry_step` is what makes that sound -- a slot that
//! holds a table pointer keeps it -- and it is this file's `RWModel::reachable`.
use concurrent_rw::{
    IsValidAtomicType, PublishPayload, RWModel, RWShared, Snapshot, WithPayload, WritePerm,
};
use vstd::prelude::*;
use vstd::raw_ptr::IsExposed;
use vstd::resource::Loc;

use crate::structs::arch_contract::{entries_per_table, slot_addr, ArchPagingMeta};
use crate::structs::entry::{entry_step, PageTableEntry};

verus! {

/// The reader half of one table page: one shared token per entry, plus what a
/// walk needs to turn an entry's frame back into a pointer.
///
/// This is also a slot's payload, which is what makes it self-referential: the
/// tokens of a page at depth `d` are escrowed in the entry at depth `d + 1`
/// that points at it.
pub struct TablePage<A: ArchPagingMeta> {
    pub slots: Seq<RWShared<PageTableEntry<A>, TablePage<A>>>,
    pub provenance: IsExposed,
    pub base: usize,
    pub frame: usize,
    pub depth: usize,
}

impl<A: ArchPagingMeta> TablePage<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: RWShared<PageTableEntry<A>, TablePage<A>>| slot.id())
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
pub struct TableWriters<A: ArchPagingMeta> {
    pub slots: Seq<WritePerm<PageTableEntry<A>>>,
}

impl<A: ArchPagingMeta> TableWriters<A> {
    pub open spec fn ids(self) -> Seq<Loc> {
        self.slots.map_values(|slot: WritePerm<PageTableEntry<A>>| slot.id())
    }
}

impl<A: ArchPagingMeta> WithPayload for PageTableEntry<A> {
    type Payload = TablePage<A>;

    /// An entry that points at a table describes the page whose tokens it
    /// escrows: the same frame, one level down.
    open spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.is_table_spec(payload.depth as nat + 1) ==> {
            &&& payload.wf()
            &&& payload.frame == self.page_frame_spec()
        }
    }
}

impl<A: ArchPagingMeta> IsValidAtomicType for PageTableEntry<A> {
    type AtomicType = usize;
}

impl<A: ArchPagingMeta> RWModel for PageTableEntry<A> {
    /// PIN, as the protocol states it: a reader that saw a table pointer may
    /// act on it later, because no writer may take it back.
    ///
    /// The depth comes from the payload rather than from the value, because the
    /// value is just a word: it is the page a slot belongs to that fixes which
    /// level it is read at, and a slot never changes level.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        &&& other.payload().depth == pair.payload().depth
        &&& entry_step(pair.value(), other.value(), pair.payload().depth as nat + 1)
    }

    /// A table entry has published its child: that is what lets a walk borrow
    /// the child's tokens outside the invariant block that produced them.
    open spec fn has_published_payload(self) -> bool {
        exists|depth: nat| self.is_table_spec(depth)
    }

    proof fn reachable_self(pair: Snapshot<Self, Self::Payload>) {
    }

    proof fn reachable_transitive(
        a: Snapshot<Self, Self::Payload>,
        b: Snapshot<Self, Self::Payload>,
        c: Snapshot<Self, Self::Payload>,
    ) {
    }

    proof fn into_from_obeys() where Self: From<Self::AtomicType> + Into<Self::AtomicType> {
        crate::specs::entry::lemma_entry_from_word::<A>(0);
        crate::specs::entry::lemma_word_from_entry::<A>(PageTableEntry::spec_from_bits(0));
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
    {
        crate::specs::entry::lemma_entry_from_word::<A>(self.view());
        crate::specs::entry::lemma_word_from_entry::<A>(self);
        PageTableEntry::<A>::lemma_bits_roundtrip(self);
    }
}

impl<A: ArchPagingMeta> PublishPayload for PageTableEntry<A> {
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    ) {
    }
}

} // verus!

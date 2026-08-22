//! How a page table slot behaves as a `concurrent_rw` value: the entry is the
//! protocol's value type, so a walk carries `RWShared` and an update carries
//! `WritePerm`.
//!
//! A table entry's payload *is* the child page it points at, so publishing an
//! entry publishes the child's reader tokens with it and a walker may descend
//! on a `&` borrow alone. `entry_step` is what makes that sound -- a slot that
//! holds a table pointer keeps it -- and it is this file's `RWModel::reachable`.
use concurrent_rw::{IsValidAtomicType, PublishPayload, RWModel, Snapshot, WithPayload};
use vstd::prelude::*;

use crate::specs::entry::{lemma_entry_from_usize, lemma_usize_from_entry};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::{entry_step, PageTableEntry};

verus! {

impl<A: ArchPagingMeta> WithPayload for PageTableEntry<A> {
    type Payload = PTPageSharedPerm<A>;

    /// An entry that points at a table describes the page whose tokens it
    /// escrows: the same frame, one level down.
    open spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.is_table_spec() ==> {
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
    /// A slot never changes which page it belongs to, so its depth is fixed.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        &&& other.payload().depth == pair.payload().depth
        &&& entry_step(pair.value(), other.value())
    }

    /// A table entry has published its child: that is what lets a walk borrow
    /// the child's tokens outside the invariant block that produced them.
    open spec fn has_published_payload(self) -> bool {
        self.is_table_spec()
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
        lemma_entry_from_usize::<A>(0);
        lemma_usize_from_entry::<A>(PageTableEntry::spec_from_bits(0));
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
     {
        lemma_entry_from_usize::<A>(self.view());
        lemma_usize_from_entry::<A>(self);
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

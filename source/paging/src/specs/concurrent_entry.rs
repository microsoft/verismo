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
use crate::structs::entry::{entry_step, PTEntry};

verus! {

impl<A: ArchPagingMeta> WithPayload for PTEntry<A> {
    /// An empty or leaf slot escrows nothing, which is why this is an
    /// `Option`: the tokens of a table page are real resources, and a slot that
    /// points at no page has none to hold. Nothing could be put there instead
    /// -- a page's tokens cannot be fabricated.
    type Payload = Option<PTPageSharedPerm<A>>;

    /// An entry that points at a table describes the page whose tokens it
    /// escrows: the page readable where the frame in this entry is mapped, one
    /// level down.
    open spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.is_table_spec() ==> {
            &&& payload is Some
            &&& payload->Some_0.wf()
            &&& payload->Some_0.base == A::spec_paddr_to_vaddr(self.page_frame_spec())
        }
    }
}

impl<A: ArchPagingMeta> IsValidAtomicType for PTEntry<A> {
    type AtomicType = usize;
}

impl<A: ArchPagingMeta> RWModel for PTEntry<A> {
    /// PIN, as the protocol states it: a reader that saw a table pointer may
    /// act on it later, because no writer may take it back.
    ///
    /// A slot that already points at a table keeps pointing at the same page,
    /// so the level of the page its payload describes is fixed from then on.
    /// Before that it escrows nothing, and an update is free to link a page of
    /// whatever level the slot's own level calls for.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        &&& pair.value().is_table_spec() ==> other.payload()->Some_0.level
            == pair.payload()->Some_0.level
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
        lemma_usize_from_entry::<A>(PTEntry::spec_from_bits(0));
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
     {
        lemma_entry_from_usize::<A>(self.view());
        lemma_usize_from_entry::<A>(self);
        PTEntry::<A>::lemma_bits_roundtrip(self);
    }
}

impl<A: ArchPagingMeta> PublishPayload for PTEntry<A> {
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    ) {
    }
}

} // verus!

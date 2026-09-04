//! A page-table slot under the read/write protocol, with its level in its type.
//!
//! [`PTEntry`] is the bit encoding and knows no level: at the leaf the hardware
//! reads bit 7 as PAT rather than PS, so the same word means different things
//! at different depths. That is fine for arithmetic on entries, but not for the
//! protocol, which must decide from the loaded word alone whether a reader may
//! borrow the slot's payload -- the child page's tokens. `Slot<A, L>` is that
//! decision made typeable: the same word, at a known level.
//!
//! Why the level has to be in the *type* rather than a ghost field: the
//! protocol requires `self === from_spec(self.into_spec())`, an entry taken to
//! its machine word and back must be itself. A ghost level is not recoverable
//! from a bare `usize`, so it would break that law. A type parameter is,
//! because the conversion is per-instantiation.
//!
//! What this buys is the reason it exists. A slot publishes its payload exactly
//! when the hardware would walk through it, and publishing is one-way: once a
//! reader may borrow a child, no writer may take it back. At the leaf that
//! would be fatal -- a 4 KiB mapping must stay clearable -- and the leaf's word
//! is indistinguishable from a table pointer. With the level in the type,
//! `Lvl<0>` simply never publishes, so the two cases never have to be told
//! apart by bits.
use core::marker::PhantomData;

use builtin_macros::{verus, verus_verify};
use concurrent_rw::{IsValidAtomicType, PublishPayload, RWModel, RWShared, Snapshot, WithPayload};
use vstd::prelude::*;
use vstd::raw_ptr::{IsExposed, PointsTo};

#[cfg(verus_only)]
use crate::structs::arch_contract::slot_addr;
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl};
use crate::structs::ptpage::PTPage;

/// One slot of a page at level `L`: a hardware entry that knows its depth.
#[verus_verify]
#[repr(transparent)]
pub struct Slot<A: ArchPagingMeta, L: LevelSpec> {
    pub entry: PTEntry<A>,
    pub dummy: PhantomData<L>,
}

impl<A: ArchPagingMeta, L: LevelSpec> From<usize> for Slot<A, L> {
    fn from(val: usize) -> Self {
        Slot { entry: PTEntry::from_bits(val), dummy: PhantomData }
    }
}

impl<A: ArchPagingMeta, L: LevelSpec> From<Slot<A, L>> for usize {
    fn from(slot: Slot<A, L>) -> usize {
        slot.entry.raw()
    }
}

verus! {

/// What a slot at this level carries, and when it carries it.
///
/// Three things vary with the level and nothing else does, so they live here
/// and the protocol impl below is written once. `A` is a parameter rather than
/// a member of [`LevelSpec`] because the payload is a page's tokens, and those
/// are architecture-shaped.
pub trait LevelPayload<A: ArchPagingMeta>: LevelSpec {
    /// The child page's reader tokens, for a level that has a child, and
    /// nothing at the leaf, which points at no table.
    type Payload;

    /// Whether a slot holding this word has published its payload: whether the
    /// hardware would walk *through* the entry into a table below.
    ///
    /// False at the leaf whatever the word says, which is what lets a 4 KiB
    /// mapping be cleared again.
    spec fn published(entry: PTEntry<A>) -> bool;

    /// What the payload of such a slot must be.
    spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool;

    /// Publishing is one-way, so `published` may not depend on any bit a writer
    /// is free to clear. Stating it here is what discharges the protocol's
    /// obligation for every level at once.
    proof fn lemma_published_needs_present(entry: PTEntry<A>)
        ensures
            Self::published(entry) ==> entry.present_spec(),
    ;
}

/// One page's reader tokens: one per slot, at a level fixed by `L`.
///
/// The level is a type parameter rather than the ghost field it used to be, so
/// that a slot's payload -- the tokens of the page one level down -- is named
/// `PagePerm<A, L::Child>` and cannot be confused with a page at any other
/// depth.
pub tracked struct PagePerm<A: ArchPagingMeta, L: LevelPayload<A>> {
    pub tracked slots: Seq<RWShared<Slot<A, L>, L::Payload>>,
    pub tracked provenance: IsExposed,
    pub ghost base: usize,
}

impl<A: ArchPagingMeta, L: LevelPayload<A>> PagePerm<A, L> {
    /// Every entry of the page is owned, and entry `index` is the token for the
    /// word the architecture puts at that index of the page at `base`.
    pub open spec fn wf(self) -> bool {
        &&& self.slots.len() == PTPage::<A>::count()
        &&& forall|index: int|
            0 <= index < self.slots.len() ==> {
                &&& (#[trigger] self.slots[index]).location()@.addr == slot_addr::<A>(
                    self.base,
                    index,
                )
                &&& self.slots[index].location()@.provenance == self.provenance@
            }
    }
}

/// The leaf publishes nothing, so it escrows nothing and needs no payload.
impl<A: ArchPagingMeta> LevelPayload<A> for Lvl<0> {
    type Payload = ();

    open spec fn published(entry: PTEntry<A>) -> bool {
        false
    }

    open spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool {
        true
    }

    proof fn lemma_published_needs_present(entry: PTEntry<A>) {
    }
}

/// An interior slot publishes exactly when the hardware would walk through it,
/// and what it publishes is the page one level down.
///
/// The four levels are written out rather than generated: they are the levels
/// the architecture has, and a macro would make the list look open-ended.
impl<A: ArchPagingMeta> LevelPayload<A> for Lvl<1> {
    type Payload = Option<PagePerm<A, <Lvl<1> as InnerLevel>::Child>>;

    open spec fn published(entry: PTEntry<A>) -> bool {
        entry.present_spec() && !entry.huge_spec()
    }

    open spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool {
        Self::published(entry) ==> {
            &&& payload is Some
            &&& payload->Some_0.wf()
            &&& payload->Some_0.base == A::spec_paddr_to_vaddr(entry.page_frame_spec())
        }
    }

    proof fn lemma_published_needs_present(entry: PTEntry<A>) {
    }
}

impl<A: ArchPagingMeta> LevelPayload<A> for Lvl<2> {
    type Payload = Option<PagePerm<A, <Lvl<2> as InnerLevel>::Child>>;

    open spec fn published(entry: PTEntry<A>) -> bool {
        entry.present_spec() && !entry.huge_spec()
    }

    open spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool {
        Self::published(entry) ==> {
            &&& payload is Some
            &&& payload->Some_0.wf()
            &&& payload->Some_0.base == A::spec_paddr_to_vaddr(entry.page_frame_spec())
        }
    }

    proof fn lemma_published_needs_present(entry: PTEntry<A>) {
    }
}

impl<A: ArchPagingMeta> LevelPayload<A> for Lvl<3> {
    type Payload = Option<PagePerm<A, <Lvl<3> as InnerLevel>::Child>>;

    open spec fn published(entry: PTEntry<A>) -> bool {
        entry.present_spec() && !entry.huge_spec()
    }

    open spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool {
        Self::published(entry) ==> {
            &&& payload is Some
            &&& payload->Some_0.wf()
            &&& payload->Some_0.base == A::spec_paddr_to_vaddr(entry.page_frame_spec())
        }
    }

    proof fn lemma_published_needs_present(entry: PTEntry<A>) {
    }
}

impl<A: ArchPagingMeta> LevelPayload<A> for Lvl<4> {
    type Payload = Option<PagePerm<A, <Lvl<4> as InnerLevel>::Child>>;

    open spec fn published(entry: PTEntry<A>) -> bool {
        entry.present_spec() && !entry.huge_spec()
    }

    open spec fn wf_payload(entry: PTEntry<A>, payload: Self::Payload) -> bool {
        Self::published(entry) ==> {
            &&& payload is Some
            &&& payload->Some_0.wf()
            &&& payload->Some_0.base == A::spec_paddr_to_vaddr(entry.page_frame_spec())
        }
    }

    proof fn lemma_published_needs_present(entry: PTEntry<A>) {
    }
}

impl<A: ArchPagingMeta, L: LevelPayload<A>> WithPayload for Slot<A, L> {
    type Payload = L::Payload;

    open spec fn wf_payload(self, payload: Self::Payload) -> bool {
        L::wf_payload(self.entry, payload)
    }
}

impl<A: ArchPagingMeta, L: LevelPayload<A>> IsValidAtomicType for Slot<A, L> {
    type AtomicType = usize;
}

impl<A: ArchPagingMeta, L: LevelPayload<A>> RWModel for Slot<A, L> {
    /// A slot is ordinary memory reached through the walk that found it, so the
    /// permission already names the address and an access shows nothing.
    type Perm = PointsTo<usize>;

    /// PIN, as the protocol states it: a reader that saw a table pointer may
    /// act on the child later, because no writer may take it back.
    ///
    /// The level agreement the untyped version had to state -- that the payload
    /// still describes a page of the same depth -- is now a type equality, so
    /// there is nothing left to say but that the frame is kept.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        L::published(pair.value().entry) ==> {
            &&& L::published(other.value().entry)
            &&& pair.value().entry.paddr_field_spec() == other.value().entry.paddr_field_spec()
        }
    }

    open spec fn has_published_payload(self) -> bool {
        L::published(self.entry)
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
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
     {
        PTEntry::<A>::lemma_bits_roundtrip(self.entry);
    }
}

impl<A: ArchPagingMeta, L: LevelPayload<A>> PublishPayload for Slot<A, L> {
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    ) {
    }
}

} // verus!

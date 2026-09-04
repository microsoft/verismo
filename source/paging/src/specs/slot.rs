//! Ghost-only specifications for [`Slot`]'s word conversions.
//!
//! `From` carries its spec through vstd's `FromSpecImpl` extension, which is
//! ghost-only, so it lives here rather than beside the executable impls -- the
//! same split `specs::entry` makes for [`PTEntry`].
use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::std_specs::convert::{FromSpec, FromSpecImpl};

use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::level::LevelSpec;
use crate::structs::slot::Slot;

verus! {

impl<A: ArchPagingMeta, L: LevelSpec> FromSpecImpl<usize> for Slot<A, L> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(val: usize) -> Slot<A, L> {
        Slot { entry: PTEntry::spec_from_bits(val), dummy: PhantomData }
    }
}

impl<A: ArchPagingMeta, L: LevelSpec> FromSpecImpl<Slot<A, L>> for usize {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(slot: Slot<A, L>) -> usize {
        slot.entry.view()
    }
}

/// Verus puts an `impl` block's members in one recursion node, so a function
/// that names these impls cannot see their definitions. Restating them as
/// lemmas outside the impls is what lets the protocol obligations be proved.
pub proof fn lemma_slot_from_usize<A: ArchPagingMeta, L: LevelSpec>(val: usize)
    ensures
        <Slot<A, L> as FromSpec<usize>>::obeys_from_spec(),
        <Slot<A, L> as FromSpec<usize>>::from_spec(val).entry == PTEntry::<A>::spec_from_bits(val),
{
}

pub proof fn lemma_usize_from_slot<A: ArchPagingMeta, L: LevelSpec>(slot: Slot<A, L>)
    ensures
        <usize as FromSpec<Slot<A, L>>>::obeys_from_spec(),
        <usize as FromSpec<Slot<A, L>>>::from_spec(slot) == slot.entry.view(),
{
}

} // verus!

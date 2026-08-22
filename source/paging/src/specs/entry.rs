//! Ghost-only specifications for [`PageTableEntry`]'s word conversions.
//!
//! `From` carries its spec through vstd's `FromSpecImpl` extension, which is
//! ghost-only, so it lives here rather than beside the executable impls.
//!
//! The two lemmas exist because Verus puts an `impl` block's members in one
//! recursion node: any function that names these impls -- `From::from` itself,
//! and the `RWModel` obligations that require them -- is grouped with them and
//! cannot see their definitions. Restating the definitions as lemmas outside
//! the impls is what lets those functions be proved.
use vstd::prelude::*;
use vstd::std_specs::convert::{FromSpec, FromSpecImpl};

use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PageTableEntry;

verus! {

impl<A: ArchPagingMeta> FromSpecImpl<usize> for PageTableEntry<A> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(val: usize) -> PageTableEntry<A> {
        PageTableEntry::spec_from_bits(val)
    }
}

impl<A: ArchPagingMeta> FromSpecImpl<PageTableEntry<A>> for usize {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(entry: PageTableEntry<A>) -> usize {
        entry.view()
    }
}

pub proof fn lemma_entry_from_usize<A: ArchPagingMeta>(val: usize)
    ensures
        <PageTableEntry<A> as FromSpec<usize>>::obeys_from_spec(),
        <PageTableEntry<A> as FromSpec<usize>>::from_spec(val)
            == PageTableEntry::<A>::spec_from_bits(val),
{
}

pub proof fn lemma_usize_from_entry<A: ArchPagingMeta>(entry: PageTableEntry<A>)
    ensures
        <usize as FromSpec<PageTableEntry<A>>>::obeys_from_spec(),
        <usize as FromSpec<PageTableEntry<A>>>::from_spec(entry) == entry.view(),
{
}

} // verus!

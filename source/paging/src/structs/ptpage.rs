//! The page-table page as a type, and how to point at one of its entries.
//!
//! A table page is named by a pointer to it rather than by a virtual address.
//! The pointer is built from the page's own tokens, so its provenance is the
//! provenance those tokens were made with -- which is what makes reading and
//! writing through it sound, and what stops a caller from handing an operation
//! an address that happens to look like a page.
//!
//! The struct itself is never constructed or dereferenced here: every access
//! goes through a token, one word at a time. What the declaration is for is
//! its size and alignment, which are what make "the entry at index `i`" a
//! pointer computation the type system agrees with.
use core::marker::PhantomData;

use vstd::prelude::*;
use vstd::raw_ptr::with_exposed_provenance;

use crate::structs::address::{Address, VirtAddr};
#[cfg(verus_only)]
use crate::structs::arch_contract::slot_addr;
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
#[cfg(verus_only)]
use crate::structs::sizes::lemma_min_page_wf;
use crate::structs::sizes::PageSize;
use crate::structs::sizes::{MinPageSize, ENTRY_COUNT, PAGE_SIZE};

verus! {

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta> {
    entries: [PTEntry<A>; ENTRY_COUNT],
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PTPage<A> {
    /// How many entries a table page holds: one page of the smallest size this
    /// build maps, filled with entries.
    pub open spec fn count() -> nat {
        ENTRY_COUNT as nat
    }

    /// A table page holds at least one entry, because the smallest page this
    /// build maps is at least 4 KiB.
    pub proof fn lemma_count_positive()
        ensures
            Self::count() > 0,
    {
        lemma_min_page_wf();
    }
}

/// The page `perm` describes, as a pointer.
///
/// `vaddr` is where the platform maps the page's frame, and the tokens say the
/// same thing; passing both is how an executable pointer is produced from a
/// ghost address without assuming anything.
pub fn page_from_vaddr<A: ArchPagingMeta>(
    vaddr: VirtAddr,
    Tracked(perm): Tracked<&PTPageSharedPerm<A>>,
) -> (ret: *mut PTPage<A>)
    requires
        perm.base == vaddr@,
    ensures
        ret@.addr == perm.base,
        ret@.provenance == perm.provenance@,
{
    with_exposed_provenance(vaddr.bits(), Tracked(perm.provenance))
}

/// A pointer to the word entry `index` of `page_ptr` occupies.
///
/// The result is a `*mut usize` because that is what a slot is: one aligned
/// machine word under the read/write protocol. The typed page pointer is what
/// says which page the word belongs to.
pub fn entry_ptr<A: ArchPagingMeta>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(perm): Tracked<&PTPageSharedPerm<A>>,
) -> (ret: *mut usize)
    requires
        perm.wf(),
        perm.base == page_ptr@.addr,
        index < PTPage::<A>::count(),
    ensures
        ret == perm.slots[index as int].location(),
{
    let ghost i = index as int;
    assert(perm.slots[i].location()@.addr == slot_addr::<A>(perm.base, i));
    let addr = page_ptr.addr() + index * core::mem::size_of::<usize>();
    with_exposed_provenance(addr, Tracked(perm.provenance))
}

} // verus!

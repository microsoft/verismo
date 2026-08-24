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
use crate::structs::arch_contract::{slot_addr, ArchPagingMeta};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::sizes::PageSize;

verus! {

/// How many address bits one level indexes, for eight-byte entries in a page
/// of `PAGE_SHIFT` bytes.
pub const PTE_SHIFT: usize = 9;

/// How many entries a table page holds.
///
/// Fixed here rather than derived from `A::MinPageSize`, because the type of a
/// page has to have a size. An architecture whose smallest page is not four
/// kibibytes cannot satisfy `level_geometry_wf`, which requires exactly this
/// many entries.
pub const ENTRY_COUNT: usize = 512;

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta> {
    entries: [PTEntry<A>; ENTRY_COUNT],
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PTPage<A> {
    /// How many entries a table page holds: one page of the architecture's smallest size, filled
    /// with entries.
    pub open spec fn count() -> nat {
        (<A::MinPageSize as PageSize>::SIZE as nat) / vstd::layout::size_of::<usize>()
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

//! The page-table page as a type, and how to point at one of its entries. The
//! struct is never dereferenced whole: every access goes through a raw pointer,
//! one word at a time, because the MMU writes those words too.
use core::marker::PhantomData;

use crate::structs::address::VirtAddr;
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::sizes::ENTRY_COUNT;

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta> {
    entries: [PTEntry<A>; ENTRY_COUNT],
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PTPage<A> {
    /// How many entries a table page holds: one page of the smallest size this
    /// build maps, filled with entries.
    pub const COUNT: usize = ENTRY_COUNT;

    /// The table page mapped at `vaddr`.
    ///
    /// # Safety
    /// A table page must be mapped there for as long as the pointer is used.
    pub unsafe fn from_vaddr(vaddr: VirtAddr) -> *mut Self {
        vaddr.as_mut_ptr::<Self>()
    }

    /// The entry at `index` of `page`.
    pub fn entry_ptr(page: *mut Self, index: usize) -> *mut PTEntry<A> {
        page.cast::<PTEntry<A>>().wrapping_add(index)
    }

    /// The entry at `index` of `page`, as the machine word it is. Entries are
    /// read and written as words so that a store the hardware may race with is
    /// a single aligned access.
    pub fn slot_ptr(page: *mut Self, index: usize) -> *mut usize {
        page.cast::<usize>().wrapping_add(index)
    }
}

//! A page table walked through raw pointers: `walk` finds where an address
//! comes to rest, `map` installs one mapping and `unmap` takes one away. A
//! mapping is never overwritten -- `map` fails instead. Entries are read and
//! written one volatile word at a time, since the MMU writes them too.
use core::marker::PhantomData;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::ptpage::PTPage;
use crate::structs::tlb::MayNeedFlush;

/// Where a walk came to rest: the entry it stopped at, the level that entry
/// sits at, and the slot it was read from, which is what an update writes.
pub struct Walk<A: ArchPagingMeta> {
    pub level: PageLevel,
    pub slot: *mut usize,
    pub entry: PTEntry<A>,
}

/// A page table rooted at a page of level `L`: `Lvl<3>` is four-level x86-64
/// paging, `Lvl<4>` five-level. The table does not own its root frame -- an
/// address space outlives the handle that walks it.
pub struct PageTable<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> {
    root: VirtAddr,
    marker: PhantomData<(A, P, L)>,
}

impl<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> PageTable<A, P, L> {
    /// A table over an existing root page.
    ///
    /// # Safety
    /// `root` must be a live level `L` table page, written by no one else.
    pub unsafe fn from_root(root: VirtAddr) -> Self {
        Self { root, marker: PhantomData }
    }

    /// A table over a freshly allocated, empty root page.
    pub fn alloc() -> Result<Self, PagingError> {
        let paddr = P::allocate_table_page()?;
        Ok(Self { root: P::paddr_to_vaddr(paddr), marker: PhantomData })
    }

    pub fn root_vaddr(&self) -> VirtAddr {
        self.root
    }

    pub fn root_paddr(&self) -> PhysAddr {
        P::vaddr_to_paddr(self.root)
    }

    /// Where `vaddr` comes to rest: the first entry the hardware would not walk
    /// through, which is a mapping, an absent entry, or an entry at the leaf
    /// level, where bit 7 is PAT rather than PS.
    pub fn walk(&self, vaddr: VirtAddr) -> Walk<A> {
        let mut level = L::LEVEL;
        let mut page = self.root;
        loop {
            let slot = slot_ptr::<A>(page, entry_index(vaddr, level));
            let entry = read_slot::<A>(slot);
            match level.child() {
                Some(child) if entry.is_table(level) => {
                    page = P::paddr_to_vaddr(PhysAddr::from(entry.address()));
                    level = child;
                }
                _ => return Walk { level, slot, entry },
            }
        }
    }

    /// The physical address `vaddr` translates to, at whatever page size maps
    /// it.
    pub fn translate(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        let walk = self.walk(vaddr);
        if !walk.entry.is_leaf(walk.level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (walk.level.size() - 1);
        Ok(PhysAddr::from(walk.entry.address() + offset))
    }

    /// Maps `vaddr` to `paddr` with a page of level `target`, building the
    /// tables between the root and `target` as needed.
    ///
    /// `flags` are the leaf's and must include `PRESENT`; the large-page bit is
    /// set here, since only this function knows whether `target` is the leaf.
    /// Tables created on the way get `parent_flags`.
    pub fn map(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        if target.depth() > L::DEPTH {
            return Err(PagingError::InvalidLevel);
        }
        let mut level = L::LEVEL;
        let mut page = self.root;
        loop {
            let slot = slot_ptr::<A>(page, entry_index(vaddr, level));
            let entry = read_slot::<A>(slot);
            if level == target {
                if entry.present() {
                    return Err(PagingError::EntryAlreadyPresent);
                }
                let addr = if shared {
                    A::make_shared_address(paddr)
                } else {
                    A::make_private_address(paddr)
                };
                let leaf = PTEntry::<A>::new_leaf(addr, flags);
                let leaf = if level.is_leaf() { leaf } else { leaf.set_huge() };
                write_slot(slot, leaf);
                return Ok(());
            }
            let child = match level.child() {
                Some(child) => child,
                None => return Err(PagingError::InvalidLevel),
            };
            page = if entry.is_table(level) {
                P::paddr_to_vaddr(PhysAddr::from(entry.address()))
            } else if entry.present() {
                // A larger page already covers this address; splitting it would
                // change a mapping someone else holds.
                return Err(PagingError::EntryAlreadyPresent);
            } else {
                let table = P::allocate_table_page()?;
                write_slot(
                    slot,
                    PTEntry::<A>::new_table(
                        A::make_private_address(table),
                        A::PTFlags::parent_flags(),
                    ),
                );
                P::paddr_to_vaddr(table)
            };
            level = child;
        }
    }

    /// Removes the mapping of `vaddr`, whatever its page size, and returns the
    /// entry that was there. Tables emptied by the removal are left in place:
    /// reclaiming one means knowing that no walker stands in it.
    pub fn unmap(
        &mut self,
        vaddr: VirtAddr,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        let walk = self.walk(vaddr);
        if !walk.entry.is_leaf(walk.level) {
            return (None, MayNeedFlush::none());
        }
        write_slot(walk.slot, PTEntry::<A>::empty());
        let start = VirtAddr::from(vaddr.bits() & !(walk.level.size() - 1));
        (Some(walk.entry), MayNeedFlush::new(start, walk.level))
    }
}

/// The word entry `index` of the table page mapped at `page` occupies.
fn slot_ptr<A: ArchPagingMeta>(page: VirtAddr, index: usize) -> *mut usize {
    PTPage::<A>::slot_ptr(page.as_mut_ptr::<PTPage<A>>(), index)
}

fn read_slot<A: ArchPagingMeta>(slot: *mut usize) -> PTEntry<A> {
    // SAFETY: `slot` addresses one word of a table page the handler mapped, and
    // a volatile read tolerates the MMU writing the accessed and dirty bits
    // under us.
    PTEntry::from_bits(unsafe { slot.read_volatile() })
}

fn write_slot<A: ArchPagingMeta>(slot: *mut usize, entry: PTEntry<A>) {
    // SAFETY: as in `read_slot`, and an aligned word-sized store is what the
    // hardware requires to see the entry whole.
    unsafe { slot.write_volatile(entry.raw()) }
}

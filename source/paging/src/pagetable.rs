//! A page table walked through raw pointers: `walk` finds where an address
//! comes to rest, `map` installs one mapping and `unmap` takes one away. Reads
//! and writes of a live entry are volatile and word-sized, since the MMU writes
//! entries too, and every mutation hands back a TLB obligation.
use core::marker::PhantomData;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::mapping::{MappingMut, MappingMutOps, MappingRef, MappingRefOps};
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::ptpage::{PTPage, PageFrame};
use crate::structs::tlb::MayNeedFlush;

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
        let (page, _paddr) = PTPage::<A, P>::alloc()?;
        Ok(Self { root: VirtAddr::from(page), marker: PhantomData })
    }

    pub fn root_vaddr(&self) -> VirtAddr {
        self.root
    }

    pub fn root_paddr(&self) -> PhysAddr {
        P::vaddr_to_paddr(self.root)
    }

    /// Where `vaddr` comes to rest: a handle on the first entry the hardware
    /// would not walk through, which is a mapping, an absent entry, or an entry
    /// at the leaf level, where bit 7 is PAT rather than PS.
    pub fn walk(&self, vaddr: VirtAddr) -> MappingRef<'_, A> {
        let mut level = L::LEVEL;
        let mut page = self.root.as_ptr::<PTPage<A, P>>();
        loop {
            let entry_ptr = PTPage::<A, P>::entry_ptr(page, entry_index(vaddr, level));
            // SAFETY: `page` is a table page of this tree, reached either from
            // the root or through a present, non-huge entry.
            let entry = unsafe { PTEntry::<A>::read_pte(entry_ptr) };
            match level.child() {
                Some(child) if entry.is_table(level) => {
                    page = PTPage::<A, P>::child_of(&entry).unwrap().cast_const();
                    level = child;
                }
                // SAFETY: as above; the handle borrows the table for `'_`.
                _ => return unsafe { MappingRef::new(level, entry_ptr) },
            }
        }
    }

    /// [`Self::walk`] with a handle that can stage and commit an edit. The
    /// exclusive borrow of the table is what keeps the entry unaliased.
    pub fn walk_mut(&mut self, vaddr: VirtAddr) -> MappingMut<'_, A> {
        let mut level = L::LEVEL;
        let mut page = self.root.as_mut_ptr::<PTPage<A, P>>();
        loop {
            let entry_ptr = PTPage::<A, P>::entry_ptr_mut(page, entry_index(vaddr, level));
            // SAFETY: as in `walk`.
            let entry = unsafe { PTEntry::<A>::read_pte(entry_ptr) };
            match level.child() {
                Some(child) if entry.is_table(level) => {
                    page = PTPage::<A, P>::child_of(&entry).unwrap();
                    level = child;
                }
                // SAFETY: as in `walk`, and `&mut self` means no other handle
                // on this table exists.
                _ => return unsafe { MappingMut::new(Some(vaddr), level, entry_ptr) },
            }
        }
    }

    /// The frame `vaddr` translates to, at whatever page size maps it.
    pub fn translate(&self, vaddr: VirtAddr) -> Result<PageFrame<A>, PagingError> {
        let mapping = self.walk(vaddr);
        let entry = mapping.read();
        let level = mapping.level();
        if !entry.is_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (level.size() - 1);
        Ok(PageFrame::new(PhysAddr::from(entry.paddr_field() + offset), level))
    }

    /// The clean physical address `vaddr` translates to.
    pub fn phys_addr(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.translate(vaddr).map(|frame| frame.address())
    }

    /// Maps `vaddr` to `paddr` with a page of level `target`, building the
    /// tables between the root and `target` as needed. A mapping is never
    /// overwritten: `map` fails instead.
    ///
    /// `flags` are the leaf's and must include `PRESENT`; the large-page bit is
    /// set for a `target` above the leaf. Tables created on the way get
    /// `parent_flags`.
    pub fn map_with_parent_flags(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        if target.depth() > L::DEPTH {
            return Err(PagingError::InvalidLevel);
        }
        self.walk_mut(vaddr).commit_no_flush(|map| {
            PTPage::<A, P>::do_map_with_parent_flags(
                map,
                vaddr,
                paddr,
                target,
                flags,
                shared,
                parent_flags,
            )
        })
    }

    /// [`Self::map_with_parent_flags`] with the architecture's default flags
    /// for the tables it creates.
    pub fn map(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_with_parent_flags(
            vaddr,
            paddr,
            target,
            flags,
            shared,
            A::PTFlags::parent_flags(),
        )
    }

    /// Removes the mapping of `vaddr`, whatever its page size, and reports the
    /// level it was mapped at. Tables emptied by the removal are left in place:
    /// reclaiming one means knowing that no walker stands in it.
    pub fn unmap(
        &mut self,
        vaddr: VirtAddr,
    ) -> (Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>) {
        let mut mapping = self.walk_mut(vaddr);
        let level = PTPage::<A, P>::do_unmap(mapping.staged());
        (level, mapping.commit())
    }

    /// Removes the mapping of `vaddr` only if it is a page of exactly
    /// `target`'s size, and returns the entry that was there.
    pub fn unmap_at(
        &mut self,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        let mut mapping = self.walk_mut(vaddr);
        let entry = PTPage::<A, P>::do_unmap_at(mapping.staged(), target);
        (entry, mapping.commit())
    }
}

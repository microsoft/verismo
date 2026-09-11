//! A page table walked through raw pointers: `walk` finds where an address
//! comes to rest, `map` installs one mapping and `unmap` takes one away. Reads
//! and writes of a live entry are volatile and word-sized, since the MMU writes
//! entries too, and every mutation hands back a TLB obligation.
use core::cmp::min;
use core::marker::PhantomData;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::mapping::{MappingMut, MappingMutOps, MappingRef, MappingRefOps};
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::ptpage::{MapSpec, PTPage, Translation};
use crate::structs::tlb::MayNeedFlush;

/// A page table rooted at a page of level `L`: `Lvl<3>` is four-level x86-64
/// paging, `Lvl<4>` five-level. The table owns its root page and frees it when
/// dropped, so a table installed in a control register must be handed to
/// [`PageTable::leak`] rather than dropped.
pub struct PageTable<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> {
    // The root is held as a physical address because that is what the hardware
    // is given; where it can be reached is the handler's business.
    root_pa: PhysAddr,
    handler: P,
    marker: PhantomData<(A, L)>,
}

impl<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> PageTable<A, P, L> {
    /// A table over an existing root page, taking ownership of it.
    ///
    /// The tree must pass [`Self::validate_page_table`]; one that does not is
    /// rejected and its root page left alone.
    ///
    /// # Safety
    /// `root_pa` must be a level `L` table page from
    /// [`PagingHandler::allocate_table_page`], written by no one else, and no
    /// other owner may free it.
    pub unsafe fn from_root(handler: P, root_pa: PhysAddr) -> Result<Self, PagingError> {
        let this = Self { root_pa, handler, marker: PhantomData };
        match this.validate_page_table() {
            Ok(()) => Ok(this),
            Err(err) => {
                // Ownership was never taken, so the root must not be freed.
                let _ = this.leak();
                Err(err)
            }
        }
    }

    /// Confirms the tree maps each of its own table pages, the root included,
    /// at the address the handler hands out for it, so that a walk still
    /// reaches them once the tree is installed.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        self.check_page_mapped(self.root_pa)?;
        // SAFETY: the root page is a level `L` table page of this tree.
        unsafe { self.check_children(self.root_page().cast_const(), L::LEVEL) }
    }

    fn check_page_mapped(&self, paddr: PhysAddr) -> Result<(), PagingError> {
        match self.phys_addr(self.handler.paddr_to_vaddr(paddr)) {
            Ok(mapped) if mapped == paddr => Ok(()),
            _ => Err(PagingError::TablePageNotSelfMapped),
        }
    }

    /// [`Self::check_page_mapped`] for every table page below `page`.
    ///
    /// # Safety
    /// `page` must be a table page of this tree, sitting at `level`.
    unsafe fn check_children(
        &self,
        page: *const PTPage<A, P>,
        level: PageLevel,
    ) -> Result<(), PagingError> {
        let Some(child_level) = level.child() else {
            return Ok(());
        };
        for idx in 0..PTPage::<A, P>::COUNT {
            // SAFETY: the caller vouches for `page`, and `idx` is in range.
            let entry = unsafe { PTPage::<A, P>::read_entry(page, idx) };
            if !entry.is_table(level) {
                continue;
            }
            self.check_page_mapped(PhysAddr::from(entry.address()))?;
            let child = PTPage::<A, P>::child_of(&self.handler, &entry).unwrap();
            // SAFETY: `child` is the table `entry` points at, one level down.
            unsafe { self.check_children(child.cast_const(), child_level) }?;
        }
        Ok(())
    }

    /// A table over a freshly allocated, empty root page.
    pub fn new(handler: P) -> Result<Self, PagingError> {
        let (_page, root_pa) = PTPage::<A, P>::alloc(&handler)?;
        Ok(Self { root_pa, handler, marker: PhantomData })
    }

    /// Gives up ownership of the root page, returning it and the handler. What
    /// a table installed in a control register needs: dropping it would free a
    /// page the hardware still walks.
    pub fn leak(self) -> (P, PhysAddr) {
        let this = core::mem::ManuallyDrop::new(self);
        let root_pa = this.root_pa;
        // SAFETY: `this` is never dropped, so the handler is moved out once.
        let handler = unsafe { core::ptr::read(&this.handler) };
        (handler, root_pa)
    }

    /// What the table calls to reach memory and to allocate.
    pub fn handler(&self) -> &P {
        &self.handler
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.root_pa
    }

    /// Where the root page is reachable, as the handler maps it.
    pub fn root_vaddr(&self) -> VirtAddr {
        self.handler.paddr_to_vaddr(self.root_pa)
    }

    fn root_page(&self) -> *mut PTPage<A, P> {
        self.root_vaddr().as_mut_ptr::<PTPage<A, P>>()
    }

    /// Where `vaddr` comes to rest: a handle on the first entry the hardware
    /// would not walk through, which is a mapping, an absent entry, or an entry
    /// at the leaf level, where bit 7 is PAT rather than PS.
    pub fn walk(&self, vaddr: VirtAddr) -> MappingRef<'_, A> {
        let mut level = L::LEVEL;
        let mut page = self.root_page().cast_const();
        loop {
            let entry_ptr = PTPage::<A, P>::entry_ptr(page, entry_index(vaddr, level));
            // SAFETY: `page` is a table page of this tree, reached either from
            // the root or through a present, non-huge entry.
            let entry = unsafe { PTEntry::<A>::read_pte(entry_ptr) };
            match level.child() {
                Some(child) if entry.is_table(level) => {
                    page = PTPage::<A, P>::child_of(&self.handler, &entry).unwrap().cast_const();
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
        let mut page = self.root_page();
        loop {
            let entry_ptr = PTPage::<A, P>::entry_ptr_mut(page, entry_index(vaddr, level));
            // SAFETY: as in `walk`.
            let entry = unsafe { PTEntry::<A>::read_pte(entry_ptr) };
            match level.child() {
                Some(child) if entry.is_table(level) => {
                    page = PTPage::<A, P>::child_of(&self.handler, &entry).unwrap();
                    level = child;
                }
                // SAFETY: as in `walk`, and `&mut self` means no other handle
                // on this table exists.
                _ => return unsafe { MappingMut::new(Some(vaddr), level, entry_ptr) },
            }
        }
    }

    /// The frame `vaddr` translates to, at whatever page size maps it.
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<A>, PagingError> {
        let mapping = self.walk(vaddr);
        let entry = mapping.read();
        let level = mapping.level();
        if !entry.is_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (level.size() - 1);
        Ok(Translation::new(PhysAddr::from(entry.paddr_field() + offset), level))
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
        let spec = MapSpec { flags, shared, parent_flags };
        let handler: *const P = &self.handler;
        self.walk_mut(vaddr).commit_no_flush(|map| {
            // SAFETY: the handler lives in this table, which the walk borrows
            // for the whole call.
            PTPage::<A, P>::do_map(unsafe { &*handler }, map, vaddr, paddr, target, spec)
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
        self.map_with_parent_flags(vaddr, paddr, target, flags, shared, A::PTFlags::parent_flags())
    }

    /// Removes the mapping of `vaddr`, whatever its page size, and reports the
    /// level it was mapped at. Tables emptied by the removal are left in place:
    /// reclaiming one means knowing that no walker stands in it.
    pub fn unmap(&mut self, vaddr: VirtAddr) -> (Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>) {
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

impl<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> Drop for PageTable<A, P, L> {
    fn drop(&mut self) {
        // SAFETY: the table owns its root page, and every constructor requires
        // it to have come from `allocate_table_page`. The tables below it are
        // not freed here: see `free_children`.
        unsafe { self.handler.deallocate_table_page(self.root_pa) };
    }
}

/// The operations whose page size is fixed: mapping a smallest page or the one
/// large page above it, and everything a range of them is built from.
impl<A: ArchPagingMeta, P: PagingHandler, L: LevelSpec> PageTable<A, P, L> {
    /// The size of the smallest page this build maps.
    pub const SMALL: PageLevel = PageLevel::Level0;

    /// The size of the large page one level up.
    pub const LARGE: PageLevel = PageLevel::Level1;

    /// Maps one smallest page.
    pub fn map_4k(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map(vaddr, paddr, Self::SMALL, flags, shared)
    }

    /// Maps one large page.
    pub fn map_2m(
        &mut self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map(vaddr, paddr, Self::LARGE, flags, shared)
    }

    /// Unmaps one smallest page, and returns the entry that mapped it.
    pub fn unmap_4k(
        &mut self,
        vaddr: VirtAddr,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        self.unmap_at(vaddr, Self::SMALL)
    }

    /// Unmaps one large page, and returns the entry that mapped it.
    pub fn unmap_2m(
        &mut self,
        vaddr: VirtAddr,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        self.unmap_at(vaddr, Self::LARGE)
    }

    /// Retags the smallest page holding `vaddr` as shared, splitting any larger
    /// page it lies in.
    pub fn set_shared_4k(
        &mut self,
        vaddr: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let handler: *const P = &self.handler;
        let mut mapping = self.walk_mut(vaddr);
        // SAFETY: the handler lives in this table, which the walk borrows.
        PTPage::<A, P>::do_set_shared(unsafe { &*handler }, mapping.staged(), vaddr, Self::SMALL)?;
        Ok(mapping.commit())
    }

    /// Retags the smallest page holding `vaddr` as private, splitting as
    /// [`Self::set_shared_4k`] does.
    pub fn set_encrypted_4k(
        &mut self,
        vaddr: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let handler: *const P = &self.handler;
        let mut mapping = self.walk_mut(vaddr);
        // SAFETY: the handler lives in this table, which the walk borrows.
        PTPage::<A, P>::do_set_encrypted(
            unsafe { &*handler },
            mapping.staged(),
            vaddr,
            Self::SMALL,
        )?;
        Ok(mapping.commit())
    }

    /// The table entry `idx` of the root points at, or `None` if it points at
    /// no table.
    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let entry_ptr = PTPage::<A, P>::entry_ptr(self.root_page().cast_const(), idx);
        // SAFETY: `idx` indexes the root page, which this table owns.
        let entry = unsafe { MappingRef::<A>::new(L::LEVEL, entry_ptr) }.read();
        if !entry.is_table(L::LEVEL) {
            return None;
        }
        Some(PhysAddr::from(entry.address()))
    }

    /// Points root entry `idx` at `subpage_pa`, a subtree the caller owns.
    /// Returns whether the entry changed. No flush is owed: the entry it
    /// replaces must have been absent.
    pub fn populate(&mut self, idx: usize, subpage_pa: PhysAddr) -> Result<bool, PagingError> {
        let desired =
            PTEntry::<A>::new(A::make_private_address(subpage_pa), A::PTFlags::parent_flags());
        let entry_ptr = PTPage::<A, P>::entry_ptr_mut(self.root_page(), idx);
        // SAFETY: `idx` indexes the root page, which this table owns, and
        // `&mut self` means no other handle on it exists.
        let mut mapping = unsafe { MappingMut::<A>::new(None, L::LEVEL, entry_ptr) };
        if mapping.staged().entry.raw() == desired.raw() {
            return Ok(false);
        }
        mapping.commit_no_flush(|map| {
            *map.entry = desired;
            Ok(true)
        })
    }

    /// Maps `[start, end)` with smallest pages, starting at `phys`.
    pub fn map_region_4k(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_region_at(start, end, phys, Self::SMALL, flags, shared)
    }

    /// Maps `[start, end)` with large pages, starting at `phys`.
    pub fn map_region_2m(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_region_at(start, end, phys, Self::LARGE, flags, shared)
    }

    /// Maps `[start, end)` with pages of one size, starting at `phys`.
    pub fn map_region_at(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        let size = target.size();
        let mut vaddr = start;
        while vaddr < end {
            self.map(vaddr, phys + (vaddr - start), target, flags, shared)?;
            vaddr = vaddr + size;
        }
        Ok(())
    }

    /// Maps `[start, end)` starting at `phys`, preferring large pages where
    /// alignment and size allow and falling back to smallest ones.
    pub fn map_region(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let large = Self::LARGE.size();
        let small = Self::SMALL.size();
        let mut vaddr = start;
        let mut paddr = phys;
        while vaddr < end {
            if vaddr.is_aligned(large)
                && paddr.is_aligned(large)
                && vaddr + large <= end
                && self.map_2m(vaddr, paddr, flags, false).is_ok()
            {
                vaddr = vaddr + large;
                paddr = paddr + large;
                continue;
            }
            self.map_4k(vaddr, paddr, flags, false)?;
            vaddr = vaddr + small;
            paddr = paddr + small;
        }
        Ok(())
    }

    /// Unmaps `[start, end)`, which must be mapped with smallest pages.
    pub fn unmap_region_4k(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        self.unmap_region_at(start, end, Self::SMALL)
    }

    /// Unmaps `[start, end)`, which must be mapped with large pages.
    pub fn unmap_region_2m(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        self.unmap_region_at(start, end, Self::LARGE)
    }

    /// Unmaps `[start, end)`, which must be mapped with pages of one size.
    pub fn unmap_region_at(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        target: PageLevel,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        let size = target.size();
        let mut flush = MayNeedFlush::none();
        let mut vaddr = start;
        while vaddr < end {
            let (_, pending) = self.unmap_at(vaddr, target);
            flush = flush.and(pending);
            vaddr = vaddr + size;
        }
        flush
    }

    /// Unmaps `[start, end)` whatever the sizes of the pages mapping it, and
    /// reports whether every page in the range was mapped. Mapped pages are
    /// unmapped either way.
    pub fn unmap_region(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> (bool, MayNeedFlush<A::TlbFlushTok>) {
        let mut flush = MayNeedFlush::none();
        let mut all_mapped = true;
        let mut vaddr = start;
        while vaddr < end {
            let (level, pending) = self.unmap(vaddr);
            flush = flush.and(pending);
            vaddr = match level {
                Some(level) => vaddr + level.size(),
                None => {
                    all_mapped = false;
                    vaddr + Self::SMALL.size()
                }
            };
        }
        (all_mapped, flush)
    }

    /// Frees the tables that `[start, end)` no longer needs, and reports
    /// whether `page` is left empty.
    ///
    /// # Safety
    /// No processor may be walking the subtree, which is the case only after
    /// the range has been unmapped and the flush discharged.
    unsafe fn free_pt_after_unmap(
        handler: &P,
        page: *mut PTPage<A, P>,
        level: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> bool {
        let Some(child_level) = level.child() else {
            // SAFETY: the caller vouches for `page`.
            return unsafe { PTPage::<A, P>::is_empty(page) };
        };
        let child_size = child_level.size();
        let mut child_start = start;
        let mut child_end = min((start + child_size).align_down(child_size), end);
        for index in entry_index(start, level)..=entry_index(end, level) {
            let entry_ptr = PTPage::<A, P>::entry_ptr_mut(page, index);
            // SAFETY: the caller vouches for `page`, and nothing else holds a
            // handle on the subtree being torn down.
            let mut mapping = unsafe { MappingMut::<A>::new(None, level, entry_ptr) };
            let entry = mapping.read();
            let Some(child) = PTPage::<A, P>::child_of(handler, &entry) else {
                continue;
            };
            // SAFETY: `child` belongs to the subtree the caller vouched for.
            if unsafe {
                Self::free_pt_after_unmap(handler, child, child_level, child_start, child_end)
            } {
                mapping.staged().entry.clear();
                // SAFETY: the entry mapped no page, only an empty table, so no
                // translation went stale.
                unsafe { mapping.commit().ignore() };
                // SAFETY: nothing links to `child` any more, and it came from
                // `allocate_table_page`.
                unsafe { handler.deallocate_table_page(PhysAddr::from(entry.address())) };
            }
            child_start = child_end;
            child_end = min(child_end + child_size, end);
        }
        // SAFETY: the caller vouches for `page`.
        unsafe { PTPage::<A, P>::is_empty(page) }
    }

    /// Frees the tables left empty by unmapping `[start, end)`.
    ///
    /// # Safety
    /// The range must already be unmapped and the flush discharged, so that no
    /// processor is walking the tables being freed.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        // SAFETY: the caller's obligation is this function's.
        let page = self.root_page();
        // SAFETY: the caller's obligation is this function's.
        unsafe { Self::free_pt_after_unmap(&self.handler, page, L::LEVEL, start, end) };
    }

    /// Frees every table below the root, leaving the root itself empty but
    /// allocated.
    ///
    /// # Safety
    /// No processor may be walking this table, and no other tree may link to
    /// its subtrees.
    pub unsafe fn free_children(&mut self) {
        // SAFETY: the caller's obligation is this function's.
        let page = self.root_page();
        // SAFETY: the caller's obligation is this function's.
        unsafe { PTPage::<A, P>::free_lvl(&self.handler, page, L::LEVEL) };
    }
}

//! An owning page table with explicit mapping and TLB operations.
//! Live accesses are atomic through lifetime-bound views; private construction
//! uses ordinary memory. Mutations return TLB obligations to the caller.
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::mapping::{
    MappingMut, MappingMutOps, MappingRef, MappingRefOps, UnmapEntryResult,
};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::policy::{KernelPolicy, PagingPolicy, UserPolicy};
use crate::structs::ptpage::{
    free_children, reclaim_path, reclaim_range, LeafUpdate, MapSpec, PTPage, PTPagePointer,
    PTPageTree, Translation,
};
use crate::structs::sizes::{entry_index, next_boundary};
use crate::structs::tlb::MayNeedFlush;

/// A page table rooted at a page of level `L`: `Lvl<3>` is four-level x86-64
/// paging, `Lvl<4>` five-level. Drop frees the root and owned descendant
/// tables, never shared subtrees or mapped data frames. Use `ManuallyDrop`
/// or [`PageTable::leak`] while external owners or hardware still use them.
pub struct PageTable<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    S: PagingPolicy = KernelPolicy,
> {
    tree: PTPageTree<A, P, L, S>,
}

/// A kernel page table that owns every attached subtree.
pub type KernelPageTable<A, P, L> = PageTable<A, P, L, KernelPolicy>;
/// A user page table that borrows the configured kernel root slots.
pub type UserPageTable<'kernel, A, P, L, const START: usize, const END: usize> =
    PageTable<A, P, L, UserPolicy<'kernel, START, END>>;

impl<A: ArchPagingMeta, P: DirectMappedAllocator, L: LevelSpec> PageTable<A, P, L> {
    /// A table that direct-maps the region the allocator allocates from, at the
    /// addresses the allocator gives for it.
    ///
    /// Mapping the whole region up front is what the tree needs to describe
    /// itself: its own pages come out of that region, as does every table it
    /// allocates later. Initialization and self-mapping checks use ordinary
    /// accesses while the entire tree is still private.
    pub fn new(allocator: P, flags: A::PTFlags) -> Result<Self, PagingError> {
        let root_pa = PTPage::<A, P>::new_direct_mapped(&allocator, L::LEVEL, flags)?;
        // SAFETY: construction produced a validated, exclusively owned, unpublished tree.
        let tree = unsafe { PTPageTree::from_root(allocator, root_pa, KernelPolicy) };
        Ok(Self { tree })
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> PageTable<A, P, L> {
    /// Validates an existing root before constructing its controller.
    /// Rejection or validation unwinding leaves the root allocated.
    /// # Safety
    /// Keep the initialized, correctly leveled, acyclic tree at clean `root_pa`
    /// accessible and aligned for `PTPage` for this controller's lifetime.
    /// Exclude other software access during mutations and entire mutable-handle
    /// lifetimes, including across roots.
    /// Shared pages must have identical virtual prefixes, never other aliases.
    /// Without `use_ad`, import presets A/D throughout the tree. Exclude all
    /// software and hardware access, and end conflicting Rust references through aliases;
    /// invalidate cached translations and paging structures before resuming use.
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(allocator: P, root_pa: PhysAddr) -> Result<Self, PagingError> {
        unsafe {
            PTPage::<A, P>::validate_tree(&allocator, root_pa, L::LEVEL, |slot| {
                PTEntryRef::from_raw(slot.cast_mut()).load()
            })
        }?;
        #[cfg(not(feature = "use_ad"))]
        // SAFETY: validation established shape; the caller excludes all users during import.
        unsafe {
            PTPage::<A, P>::normalize_ad_tree(&allocator, root_pa, L::LEVEL);
        }
        // SAFETY: validation establishes shape; ownership and quiescence are the caller's duty.
        let tree = unsafe { PTPageTree::from_root(allocator, root_pa, KernelPolicy) };
        Ok(Self { tree })
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingPolicy> PageTable<A, P, L, S> {
    /// Confirms the tree maps each of its own table pages, the root included,
    /// at the address the allocator hands out for it, so that a walk still
    /// reaches them once the tree is installed.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        // SAFETY: this borrow keeps the tree accessible throughout validation.
        unsafe {
            PTPage::<A, P>::validate_tree(
                &self.tree.allocator,
                self.tree.root_paddr(),
                L::LEVEL,
                |slot| PTEntryRef::from_raw(slot.cast_mut()).load(),
            )
        }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> PageTable<A, P, L> {
    /// Borrows existing subtrees at `START..END`; the entire range becomes immutable.
    /// Initialize shared root slots before copying if later growth must be visible.
    /// # Safety
    /// `allocator` must resolve shared physical addresses to the same table pages as `other`.
    /// Shared pages must remain allocated while either tree links to them.
    /// Exclude access through every alias during mutations and the entire
    /// lifetime of any mutable mapping handle. Cleanup through either tree
    /// requires removing all other parent links to every reclaimed page.
    pub unsafe fn new_from_sharing_top<'kernel, const START: usize, const END: usize>(
        allocator: P,
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, A, P, L, START, END>, PagingError> {
        let policy = UserPolicy::<START, END>::new();
        let mut tree = PTPageTree::new_root(allocator, policy)?;
        {
            // SAFETY: the fresh destination has no software or hardware users.
            let page = unsafe { tree.page_mut() };
            for idx in START..END {
                let entry = other.root_view().load(idx);
                if entry.is_table(L::LEVEL) {
                    *page.entry_mut(idx) = entry.for_publication();
                }
            }
        }
        let this = PageTable { tree };
        this.validate_page_table()?;
        Ok(this)
    }

    /// Gives up ownership of the tree, returning its root and allocator. What
    /// a table installed in a control register needs: dropping it would free a
    /// page the hardware still walks. A borrowed root remains borrowed.
    pub fn leak(self) -> (P, PhysAddr) {
        let (allocator, _, root_pa) = self.leak_parts();
        (allocator, root_pa)
    }

    /// Raw staged edits are restricted to privileged controllers.
    /// # Safety
    /// Committed entries must preserve the tree's level, validity and ownership
    /// invariants. New table links transfer exclusive ownership of initialized,
    /// correctly leveled, allocator-allocated subtrees; no aliases or cycles.
    /// Coordinate hardware access and flushes for every published change.
    ///
    /// ```compile_fail,E0133
    /// use paging::address::VirtAddr;
    /// use paging::level::LevelSpec;
    /// use paging::os_contract::PagingAllocator;
    /// use paging::pagetable::PageTable;
    /// use paging::ArchPagingMeta;
    ///
    /// fn raw_edit<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec>(
    ///     table: &mut PageTable<A, P, L>,
    ///     address: VirtAddr,
    /// ) {
    ///     let _ = table.walk_mut(address);
    /// }
    /// ```
    pub unsafe fn walk_mut(&mut self, vaddr: VirtAddr) -> MappingMut<'_, A> {
        self.walk_mut_inner(vaddr)
    }

    /// Installs an owned subtree in an absent root slot.
    /// # Safety
    /// The subtree must be initialized, correctly leveled, acyclic, mapped and
    /// allocated by this controller's allocator.
    /// A new installation transfers its ownership; no other parent may link to it.
    /// Without `use_ad`, new subtrees must be quiesced while their A/D bits are
    /// preset; invalidate any cached state before hardware can use them.
    pub unsafe fn populate(
        &mut self,
        idx: usize,
        subpage_pa: PhysAddr,
    ) -> Result<bool, PagingError> {
        assert!(idx < PTPage::<A, P>::COUNT);
        if L::LEVEL.is_leaf() {
            return Err(PagingError::InvalidLevel);
        }
        let desired = PTEntry::<A>::new_table(
            A::make_private_address(subpage_pa),
            A::PTFlags::parent_flags(),
        );
        let view = self.root_view();
        let slot = view.entry(idx);
        let entry = slot.load();
        if entry.is_table(L::LEVEL) && entry.address() == subpage_pa.bits() {
            return Ok(false);
        }
        if entry.is_table(L::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent {
                frame: PhysAddr::from(entry.address()),
                level: L::LEVEL,
            });
        }
        #[cfg(not(feature = "use_ad"))]
        // SAFETY: a new subtree is correctly leveled and quiesced by the caller.
        unsafe {
            PTPage::<A, P>::normalize_ad_tree(
                &self.tree.allocator,
                subpage_pa,
                L::LEVEL.child().unwrap(),
            );
        }
        slot.store(desired);
        Ok(true)
    }
}

impl<
        'kernel,
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: LevelSpec,
        const START: usize,
        const END: usize,
    > PageTable<A, P, L, UserPolicy<'kernel, START, END>>
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (P, UserPolicy<'kernel, START, END>, PhysAddr) {
        self.leak_parts()
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingPolicy> PageTable<A, P, L, S> {
    fn leak_parts(self) -> (P, S, PhysAddr) {
        self.tree.into_parts()
    }

    pub fn policy(&self) -> &S {
        self.tree.policy()
    }

    pub fn owns_top_entry(&self, index: usize) -> bool {
        self.tree.policy().owns_top_entry(index)
    }

    /// [`Self::map_region`] over what the region does not already map, leaving
    /// mappings that are already the wanted ones alone. Widening an old direct
    /// map into a larger new one needs it, the two overlapping.
    pub fn map_region_if_absent(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        let large = Self::LARGE.size();
        let mut vaddr = start;
        while vaddr < end {
            let paddr = phys.checked_add(vaddr - start).ok_or(PagingError::InvalidRange)?;
            if vaddr.is_aligned(large)
                && paddr.is_aligned(large)
                && end - vaddr >= large
                && self.map_2m(vaddr, paddr, flags, false).is_ok()
            {
                vaddr = next_boundary(vaddr, Self::LARGE, end);
                continue;
            }
            match self.map_4k(vaddr, paddr, flags, false) {
                Ok(()) => vaddr = next_boundary(vaddr, Self::SMALL, end),
                // Already the mapping we wanted: step over the whole page it
                // is part of, however large that page is.
                Err(PagingError::EntryAlreadyPresent { frame, level }) if frame == paddr => {
                    vaddr = next_boundary(vaddr, level, end);
                }
                Err(err) => return Err(err),
            }
        }
        Ok(())
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    fn root_view(&self) -> PTPagePointer<'_, A, P> {
        self.tree.root()
    }

    /// Where `vaddr` comes to rest: a handle on the first entry the hardware
    /// would not walk through, which is a mapping, an absent entry, or an entry
    /// at the leaf level, where bit 7 is PAT rather than PS.
    ///
    /// ```compile_fail,E0502
    /// use paging::address::VirtAddr;
    /// use paging::level::LevelSpec;
    /// use paging::mapping::MappingRefOps;
    /// use paging::os_contract::PagingAllocator;
    /// use paging::pagetable::KernelPageTable;
    /// use paging::ArchPagingMeta;
    ///
    /// fn reclaim<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec>(
    ///     table: &mut KernelPageTable<A, P, L>,
    ///     address: VirtAddr,
    /// ) {
    ///     let entry = table.walk(address);
    ///     unsafe { table.free_page_table_by_addr(address) };
    ///     let _ = entry.read();
    /// }
    /// ```
    pub fn walk(&self, vaddr: VirtAddr) -> MappingRef<'_, A> {
        let (entry, level) = self.walk_entry(vaddr);
        MappingRef::from_view(level, entry)
    }

    fn walk_entry(&self, vaddr: VirtAddr) -> (PTEntryRef<'_, A>, PageLevel) {
        let observed = self.root_view().walk(vaddr);
        (observed.entry(), observed.page.level())
    }

    fn walk_mut_inner(&mut self, vaddr: VirtAddr) -> MappingMut<'_, A> {
        let (entry, level) = self.walk_entry(vaddr);
        MappingMut::from_view(Some(vaddr), level, entry)
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
        Ok(Translation::new(
            PhysAddr::from((entry.paddr_field() & !(level.size() - 1)) + offset),
            level,
        ))
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
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target.depth() > L::DEPTH {
            return Err(PagingError::InvalidLevel);
        }
        let spec = MapSpec { flags, shared, parent_flags };
        let (entry, level) = self.walk_entry(vaddr);
        if level > target && !entry.load().present() {
            let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
            let prepared = PTPageTree::<A, P>::new(self.tree.allocator.clone(), child_level)?;
            let observed = prepared.root().walk(vaddr);
            MappingMut::from_view(Some(vaddr), observed.page.level(), observed.entry())
                .commit_no_flush(|map| {
                    PTPage::<A, P>::do_map(&self.tree.allocator, map, vaddr, paddr, target, spec)
                })?;
            entry.store(PTEntry::new_table(
                A::make_private_address(prepared.root_paddr()),
                A::filter_flags(parent_flags),
            ));
            prepared.release();
            return Ok(());
        }
        MappingMut::from_view(Some(vaddr), level, entry).commit_no_flush(|map| {
            PTPage::<A, P>::do_map(&self.tree.allocator, map, vaddr, paddr, target, spec)
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
    pub fn unmap(
        &mut self,
        vaddr: VirtAddr,
    ) -> Result<(Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>), PagingError> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        Ok(self.unmap_inner(vaddr))
    }

    fn unmap_inner(
        &mut self,
        vaddr: VirtAddr,
    ) -> (Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>) {
        let (entry, level) = self.walk_entry(vaddr);
        if !entry.load().is_leaf(level) {
            return (None, MayNeedFlush::none());
        }
        entry.swap(PTEntry::empty());
        (Some(level), MayNeedFlush::new(vaddr, level))
    }

    /// Removes the mapping of `vaddr` only if it is a page of exactly
    /// `target`'s size, and returns the entry that was there.
    pub fn unmap_at(&mut self, vaddr: VirtAddr, target: PageLevel) -> UnmapEntryResult<A> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        Ok(self.unmap_at_inner(vaddr, target))
    }

    fn unmap_at_inner(
        &mut self,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        let (entry, level) = self.walk_entry(vaddr);
        if level != target || !entry.load().is_leaf(level) {
            return (None, MayNeedFlush::none());
        }
        (Some(entry.swap(PTEntry::empty())), MayNeedFlush::new(vaddr, target))
    }

    /// Splits a huge leaf without changing its mappings. The complete split
    /// path is prepared privately, so allocation failure leaves the leaf intact.
    /// `vaddr` may be any address within the selected mapping.
    /// Splitting uses the architecture's required publication and flush order.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split(
        &mut self,
        vaddr: VirtAddr,
        target: PageLevel,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        match self.edit_leaf(vaddr, target, LeafUpdate::Split, all_cpus) {
            Ok(flush) => Ok(flush),
            Err(PagingError::NotLeafEntry) => Ok(MayNeedFlush::none()),
            Err(err) => Err(err),
        }
    }

    /// Replaces flags on exactly one target-sized page, splitting a larger
    /// leaf if needed. Frame, tags, PAT and A/D history are retained.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    pub fn mprotect(
        &mut self,
        vaddr: VirtAddr,
        target: PageLevel,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        if !vaddr.is_aligned(target.size()) {
            return Err(PagingError::InvalidAddress);
        }
        self.edit_leaf(vaddr, target, LeafUpdate::Protect(flags), all_cpus)
    }

    /// Protects a page-aligned range. On error, earlier edits remain applied
    /// and their flush obligation is returned alongside the error.
    /// Page-size transitions share one architecture-ordered synchronous flush.
    /// `all_cpus` selects its scope as in [`Self::split`].
    pub fn mprotect_range(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<A::TlbFlushTok>) {
        let flush = MayNeedFlush::none();
        if let Err(error) = self.tree.policy().check_range(L::LEVEL, start, end) {
            return (Err(error), flush);
        }
        if start > end
            || !start.is_aligned(Self::SMALL.size())
            || !end.is_aligned(Self::SMALL.size())
        {
            return (Err(PagingError::InvalidRange), flush);
        }
        if !flags.present() {
            return (Err(PagingError::InvalidFlags), flush);
        }
        // SAFETY: the exclusive borrow pins the tree and excludes software writers.
        unsafe { PTPage::<A, P>::mprotect_range(self.root_view(), start, end, flags, all_cpus) }
    }

    fn edit_leaf(
        &mut self,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        let (entry, level) = self.walk_entry(vaddr);
        // SAFETY: the exclusive borrow pins the entry and excludes software writers.
        unsafe {
            PTPage::<A, P>::edit_leaf(
                &self.tree.allocator,
                entry,
                level,
                vaddr,
                target,
                update,
                all_cpus,
            )
        }
    }
}

/// The operations whose page size is fixed: mapping a smallest page or the one
/// large page above it, and everything a range of them is built from.
impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingPolicy> PageTable<A, P, L, S> {
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
    pub fn unmap_4k(&mut self, vaddr: VirtAddr) -> UnmapEntryResult<A> {
        self.unmap_at(vaddr, Self::SMALL)
    }

    /// Unmaps one large page, and returns the entry that mapped it.
    pub fn unmap_2m(&mut self, vaddr: VirtAddr) -> UnmapEntryResult<A> {
        self.unmap_at(vaddr, Self::LARGE)
    }

    /// Retags the smallest page holding `vaddr` as shared, splitting any larger
    /// page it lies in.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    pub fn set_shared_4k(
        &mut self,
        vaddr: VirtAddr,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.edit_leaf(vaddr, Self::SMALL, LeafUpdate::UpdateEncryption(true), all_cpus)
    }

    /// Retags the smallest page holding `vaddr` as private, splitting as
    /// [`Self::set_shared_4k`] does.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    pub fn set_encrypted_4k(
        &mut self,
        vaddr: VirtAddr,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.edit_leaf(vaddr, Self::SMALL, LeafUpdate::UpdateEncryption(false), all_cpus)
    }

    /// The table entry `idx` of the root points at, or `None` if it points at
    /// no table.
    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        assert!(idx < PTPage::<A, P>::COUNT);
        let view = self.root_view();
        let entry = view.load(idx);
        if !entry.is_table(view.level()) {
            return None;
        }
        Some(PhysAddr::from(entry.address()))
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
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        let mut vaddr = start;
        while vaddr < end {
            let paddr = phys.checked_add(vaddr - start).ok_or(PagingError::InvalidRange)?;
            self.map(vaddr, paddr, target, flags, shared)?;
            vaddr = next_boundary(vaddr, target, end);
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
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        let large = Self::LARGE.size();
        let mut vaddr = start;
        while vaddr < end {
            let paddr = phys.checked_add(vaddr - start).ok_or(PagingError::InvalidRange)?;
            if vaddr.is_aligned(large)
                && paddr.is_aligned(large)
                && end - vaddr >= large
                && self.map_2m(vaddr, paddr, flags, false).is_ok()
            {
                vaddr = next_boundary(vaddr, Self::LARGE, end);
                continue;
            }
            self.map_4k(vaddr, paddr, flags, false)?;
            vaddr = next_boundary(vaddr, Self::SMALL, end);
        }
        Ok(())
    }

    /// Unmaps `[start, end)`, which must be mapped with smallest pages.
    pub fn unmap_region_4k(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.unmap_region_at(start, end, Self::SMALL)
    }

    /// Unmaps `[start, end)`, which must be mapped with large pages.
    pub fn unmap_region_2m(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.unmap_region_at(start, end, Self::LARGE)
    }

    /// Unmaps `[start, end)`, which must be mapped with pages of one size.
    pub fn unmap_region_at(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        target: PageLevel,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        if !start.is_aligned(target.size()) || !end.is_aligned(target.size()) {
            return Err(PagingError::InvalidRange);
        }
        let size = target.size();
        let mut flush = MayNeedFlush::none();
        let mut vaddr = start;
        while vaddr < end {
            let (_, pending) = self.unmap_at_inner(vaddr, target);
            flush = flush.and(pending);
            vaddr = vaddr + size;
        }
        Ok(flush)
    }

    /// Unmaps `[start, end)` whatever the sizes of the pages mapping it, and
    /// reports whether every page in the range was mapped. Mapped pages are
    /// unmapped either way.
    pub fn unmap_region(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(bool, MayNeedFlush<A::TlbFlushTok>), PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        let mut flush = MayNeedFlush::none();
        let mut all_mapped = true;
        let mut vaddr = start;
        while vaddr < end {
            let (level, pending) = self.unmap_inner(vaddr);
            flush = flush.and(pending);
            all_mapped &= level.is_some();
            vaddr = next_boundary(vaddr, level.unwrap_or(Self::SMALL), end);
        }
        Ok((all_mapped, flush))
    }

    /// Frees owned tables left empty in `[start, end)`, skipping shared subtrees.
    ///
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        assert!(start <= end);
        if start < end {
            let span = L::LEVEL.size() * PTPage::<A, P>::COUNT;
            let first = start.bits() & (span - 1);
            let last = ((end.bits() - 1) & (span - 1)) + 1;
            assert!(first < last, "range wraps the root's address space");
            // SAFETY: the caller supplies ownership and excludes all walkers.
            unsafe {
                reclaim_range(
                    &self.root_view(),
                    first,
                    last,
                    |index| self.tree.policy().owns_top_entry(index),
                    |entry| !entry.present(),
                )
            };
        }
    }

    /// Frees the tables left empty by unmapping `vaddr`, walking the one path
    /// down to it rather than a range, and reports how many it freed.
    /// Tables still holding mappings remain allocated.
    ///
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_addr(&mut self, vaddr: VirtAddr) -> usize {
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, L::LEVEL)) {
            return 0;
        }
        // SAFETY: the caller's obligation is this function's.
        unsafe { reclaim_path(&self.root_view(), vaddr, |entry| !entry.present()) }
    }

    /// Frees owned tables below the root; borrowed root entries remain intact.
    ///
    /// # Safety
    /// Every owned child table must come from this allocator, with no other parent
    /// links. Exclude all other walkers and invalidate cached table pointers
    /// before reusing pages or resuming hardware walks.
    pub unsafe fn free_children(&mut self) {
        // SAFETY: the caller supplies ownership and quiescence for every selected subtree.
        unsafe {
            free_children(&self.root_view(), |index| self.tree.policy().owns_top_entry(index))
        };
    }
}

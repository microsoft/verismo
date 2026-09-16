//! The `pagetable` API with concurrent walks and serialized entry updates.
//! Shared borrows pin table pages; exclusive borrows permit reclamation.
//! An external RwLock can provide those borrows. It does not fence hardware
//! walkers: the embedder supplies synchronous TLB hooks and hardware quiescence.
#![doc = include_str!("../concurrency.md")]

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::mapping::UnmapEntryResult;
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy, UserPolicy};
use crate::structs::ptpage::{
    free_children, reclaim_path, reclaim_range, LeafUpdate, PTPage, PTPagePointer, PTPageTree,
    Translation, WalkResult,
};
use crate::structs::sizes::{entry_index, next_boundary};
use crate::structs::tlb::MayNeedFlush;

/// A write-permission lock keyed by physical table page. Keys may share one lock or
/// select per-page/striped locks; paging never holds two guards at once.
/// Guards borrow protected metadata/permissions, never live PTE storage.
///
/// # Safety
/// Guards for the same page must exclude each other, acquiring on `lock` and
/// releasing on drop without panicking. Keys and exclusion must remain stable
/// across every tree sharing those pages, including during unwinding.
pub unsafe trait LockSpec<T> {
    /// A borrowed guard excluding writers for one keyed table page.
    type Guard<'a>: Deref<Target = T> + DerefMut
    where
        Self: 'a,
        T: 'a;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_>;
}

/// An atomic observation, not a reference to a live entry or a pinned frame.
/// Another update can invalidate its translation immediately.
pub struct MappingSnapshot<A: ArchPagingMeta> {
    entry: PTEntry<A>,
    level: PageLevel,
}

/// Internal outcome used to restart a range walk after a concurrent split.
enum RangeUpdateError {
    Retry,
    Split(usize),
    Paging(PagingError),
}

impl<A: ArchPagingMeta> MappingSnapshot<A> {
    pub fn read(&self) -> PTEntry<A> {
        self.entry
    }

    pub fn level(&self) -> PageLevel {
        self.level
    }
}

/// Shared access permits walk, map, unmap and split, but never removes an
/// installed table pointer. Freeing needs `&mut self` and hardware exclusion.
/// Drop frees the root and owned descendant tables, never shared subtrees or data
/// frames. Externally managed or hardware-active trees need `ManuallyDrop` or `leak`.
pub struct PageTable<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    W,
    T = (),
    S: PagingOwnershipPolicy = KernelPolicy,
> {
    tree: PTPageTree<A, P, L, S>,
    wperms: W,
    marker: PhantomData<T>,
}

/// A concurrent kernel page table using `W` as its PTE write-permission domain.
pub type KernelPageTable<A, P, L, W, T = ()> = PageTable<A, P, L, W, T, KernelPolicy>;
/// A concurrent user page table borrowing the configured kernel root slots.
pub type UserPageTable<'kernel, A, P, L, W, const START: usize, const END: usize, T = ()> =
    PageTable<A, P, L, W, T, UserPolicy<'kernel, START, END>>;

impl<A, P, L, W, T> PageTable<A, P, L, W, T>
where
    A: ArchPagingMeta,
    P: DirectMappedAllocator,
    L: LevelSpec,
    W: LockSpec<T>,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(wperms: W, flags: A::PTFlags) -> Result<Self, PagingError> {
        let root_pa = PTPage::<A, P>::new_direct_mapped(L::LEVEL, flags)?;
        // SAFETY: construction produced a validated, exclusively owned, unpublished tree.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }
}

impl<A, P, L, W, T> PageTable<A, P, L, W, T>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    W: LockSpec<T>,
{
    /// Validates an existing root before constructing its controller.
    /// Rejection or validation unwinding leaves the root allocated.
    /// # Safety
    /// Keep the initialized, correctly leveled, acyclic tree at clean `root_pa`
    /// accessible and aligned for `PTPage` for this controller's lifetime.
    /// Every software user must follow this atomic-access, content-lock and
    /// lifetime protocol. Shared pages must
    /// appear at identical virtual prefixes, never at different aliases.
    /// Without `use_ad`, import presets A/D throughout the tree. Exclude all
    /// software and hardware access, and end conflicting Rust references through aliases;
    /// invalidate cached translations and paging structures before resuming use.
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(wperms: W, root_pa: PhysAddr) -> Result<Self, PagingError> {
        unsafe {
            PTPage::<A, P>::validate_tree(root_pa, L::LEVEL, |slot| {
                PTEntryRef::from_raw(slot.cast_mut()).load()
            })
        }?;
        #[cfg(not(feature = "use_ad"))]
        // SAFETY: validation established shape; the caller excludes all users during import.
        unsafe {
            PTPage::<A, P>::normalize_ad_tree(root_pa, L::LEVEL);
        }
        // SAFETY: validation establishes shape; ownership and quiescence are the caller's duty.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }

    /// Borrows existing subtrees at `START..END`; the entire range becomes immutable.
    /// Initialize shared root slots before copying if later growth must be visible.
    /// # Safety
    /// `P` must resolve shared physical addresses to the same table pages as `other`.
    /// Shared pages must outlive both trees at identical virtual prefixes,
    /// use the same content-lock domain, and not be reclaimed while in use.
    pub unsafe fn new_from_sharing_top<'kernel, const START: usize, const END: usize>(
        wperms: W,
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, A, P, L, W, START, END, T>, PagingError> {
        let policy = UserPolicy::<START, END>::new();
        let mut tree = PTPageTree::new_root(policy)?;
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
        let this = PageTable { tree, wperms, marker: PhantomData };
        this.validate_page_table()?;
        Ok(this)
    }

    /// Gives up the tree and returns its root and content-lock domain.
    /// A borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> (W, PhysAddr) {
        let (wperms, _, root_pa) = self.leak_parts();
        (wperms, root_pa)
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
        if L::LEVEL.is_leaf() {
            return Err(PagingError::InvalidLevel);
        }
        let desired =
            PTEntry::new_table(A::make_private_address(subpage_pa), A::PTFlags::parent_flags());
        let slot = self.root_view().entry(idx);
        let _guard = self.wperms.lock(self.tree.root_paddr());
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
            PTPage::<A, P>::normalize_ad_tree(subpage_pa, L::LEVEL.child().unwrap());
        }
        // Only an absent slot changes; ownership transfers with publication.
        slot.store(desired);
        Ok(true)
    }
}

impl<'kernel, A, P, L, W, T, const START: usize, const END: usize>
    PageTable<A, P, L, W, T, UserPolicy<'kernel, START, END>>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    W: LockSpec<T>,
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (W, UserPolicy<'kernel, START, END>, PhysAddr) {
        self.leak_parts()
    }
}

impl<A, P, L, W, T, S> PageTable<A, P, L, W, T, S>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    W: LockSpec<T>,
    S: PagingOwnershipPolicy,
{
    pub const SMALL: PageLevel = PageLevel::Level0;
    pub const LARGE: PageLevel = PageLevel::Level1;

    fn leak_parts(self) -> (W, S, PhysAddr) {
        let (policy, root_pa) = self.tree.into_parts();
        (self.wperms, policy, root_pa)
    }

    pub fn policy(&self) -> &S {
        self.tree.policy()
    }

    pub fn owns_top_entry(&self, index: usize) -> bool {
        self.tree.policy().owns_top_entry(index)
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    fn root_view(&self) -> PTPagePointer<'_, A, P> {
        self.tree.root()
    }

    /// A leaf/absent-entry snapshot. It holds no content lock and gives no
    /// authority to dereference or free the translated data frame.
    #[inline(always)]
    pub fn walk(&self, vaddr: VirtAddr) -> MappingSnapshot<A> {
        let position = self.tree.walk(vaddr);
        MappingSnapshot { entry: position.observed, level: position.page.level() }
    }

    /// Returns an unlocked target slot, without replacing existing leaves or subtrees.
    fn walk_or_alloc(
        &self,
        vaddr: VirtAddr,
        target: PageLevel,
        parent_flags: A::PTFlags,
    ) -> Result<WalkResult<'_, A, P>, PagingError> {
        let mut mapping = self.root_view().walk(vaddr);
        while mapping.page.level() > target {
            let level = mapping.page.level();
            let pte_ref = mapping.entry();
            let pte_val = pte_ref.load();
            if !pte_val.is_table(level) {
                if pte_val.present() {
                    return Err(Self::already_present(pte_val, level, vaddr));
                }
                let child_level = level.child().unwrap();
                let mut prepared = PTPageTree::<A, P>::new(child_level)?;
                prepared.grow(vaddr, target, parent_flags)?;
                let paddr = mapping.page_paddr();
                {
                    // Declared after preparation so a losing path is reclaimed after unlocking.
                    let _guard = self.wperms.lock(paddr);
                    let exclusive_pte_val = pte_ref.load();
                    if !exclusive_pte_val.is_table(level) {
                        if exclusive_pte_val.present() {
                            return Err(Self::already_present(exclusive_pte_val, level, vaddr));
                        }
                        pte_ref.store(PTEntry::new_table(
                            A::make_private_address(prepared.root_paddr()),
                            parent_flags,
                        ));
                        prepared.release();
                    }
                }
            }
            mapping = mapping.page.walk(vaddr);
        }
        if mapping.page.level() < target {
            Err(PagingError::NotLeafEntry)
        } else {
            Ok(mapping)
        }
    }

    #[inline(always)]
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<A>, PagingError> {
        let snapshot = self.walk(vaddr);
        if snapshot.level == PageLevel::Level0 {
            if !snapshot.entry.present() {
                return Err(PagingError::NotMapped);
            }
            let offset = vaddr.bits() & (Self::SMALL.size() - 1);
            return Ok(Translation::new(
                PhysAddr::from((snapshot.entry.paddr_field() & !(Self::SMALL.size() - 1)) + offset),
                snapshot.level,
            ));
        }
        if !snapshot.entry.is_leaf(snapshot.level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (snapshot.level.size() - 1);
        Ok(Translation::new(
            PhysAddr::from((snapshot.entry.paddr_field() & !(snapshot.level.size() - 1)) + offset),
            snapshot.level,
        ))
    }

    #[inline(always)]
    pub fn phys_addr(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.translate(vaddr).map(|frame| frame.address())
    }

    /// Checks self-mappings using atomic observations. A whole-tree result
    /// requires the caller to exclude concurrent content updates.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        // SAFETY: this borrow pins every followed table; all observations are atomic.
        unsafe {
            PTPage::<A, P>::validate_tree(self.tree.root_paddr(), L::LEVEL, |slot| {
                PTEntryRef::from_raw(slot.cast_mut()).load()
            })
        }
    }

    /// Maps an absent entry, publishing zeroed intermediate tables as needed.
    /// A failure may leave empty intermediate tables for later cleanup.
    /// Existing leaves and table pointers are never replaced.
    pub fn map_with_parent_flags(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        assert!(vaddr.is_aligned(target.size()) && paddr.is_aligned(target.size()));
        assert!(flags.present());
        let flags = A::filter_flags(flags);
        let parent_flags = A::filter_flags(parent_flags);
        let mapping = self.walk_or_alloc(vaddr, target, parent_flags)?;
        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        let entry = mapping.entry().load();
        if entry.is_table(mapping.page.level()) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(Self::already_present(entry, mapping.page.level(), vaddr));
        }
        let addr =
            if shared { A::make_shared_address(paddr) } else { A::make_private_address(paddr) };
        let flags = if target.is_leaf() { flags } else { flags.with(A::PTFlags::HUGE) };
        mapping.entry().store(PTEntry::new(addr, flags));
        Ok(())
    }

    fn already_present(entry: PTEntry<A>, level: PageLevel, vaddr: VirtAddr) -> PagingError {
        PagingError::EntryAlreadyPresent {
            frame: PhysAddr::from(
                (entry.address() & !(level.size() - 1)) + (vaddr.bits() & (level.size() - 1)),
            ),
            level,
        }
    }

    pub fn map(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_with_parent_flags(vaddr, paddr, target, flags, shared, A::PTFlags::parent_flags())
    }

    pub fn map_4k(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map(vaddr, paddr, Self::SMALL, flags, shared)
    }

    pub fn map_2m(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map(vaddr, paddr, Self::LARGE, flags, shared)
    }

    /// Clears the leaf observed under its page lock, retaining every table.
    /// If split wins the race, this removes the finer leaf found afterwards.
    pub fn unmap(
        &self,
        vaddr: VirtAddr,
    ) -> Result<(Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>), PagingError> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        Ok(self.unmap_inner(vaddr))
    }

    fn unmap_inner(&self, vaddr: VirtAddr) -> (Option<PageLevel>, MayNeedFlush<A::TlbFlushTok>) {
        for _ in 0..=L::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            let entry = mapping.entry().load();
            if entry.is_table(mapping.page.level()) {
                continue;
            }
            if !entry.is_leaf(mapping.page.level()) {
                return (None, MayNeedFlush::none());
            }
            mapping.entry().swap(PTEntry::empty());
            return (Some(mapping.page.level()), MayNeedFlush::new(vaddr, mapping.page.level()));
        }
        unreachable!("page-table unmapping exceeded the tree depth")
    }

    #[inline(always)]
    pub fn unmap_at(&self, vaddr: VirtAddr, target: PageLevel) -> UnmapEntryResult<A> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        if target == Self::SMALL {
            return Ok(self.unmap_4k_inner(vaddr));
        }
        Ok(self.unmap_at_inner(vaddr, target))
    }

    #[inline(always)]
    fn unmap_4k_inner(
        &self,
        vaddr: VirtAddr,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.unmap_at_inner(vaddr, Self::SMALL);
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        if !mapping.entry().load().is_leaf(Self::SMALL) {
            return (None, MayNeedFlush::none());
        }
        let entry = mapping.entry().swap(PTEntry::empty());
        (Some(entry), MayNeedFlush::new_4k(vaddr))
    }

    fn unmap_at_inner(
        &self,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> (Option<PTEntry<A>>, MayNeedFlush<A::TlbFlushTok>) {
        for _ in 0..=L::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return (None, MayNeedFlush::none());
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            let entry = mapping.entry().load();
            if entry.is_table(mapping.page.level()) {
                continue;
            }
            if mapping.page.level() != target || !entry.is_leaf(mapping.page.level()) {
                return (None, MayNeedFlush::none());
            }
            // Swap captures even hardware A/D changes since the load.
            let entry = mapping.entry().swap(PTEntry::empty());
            return (Some(entry), MayNeedFlush::new(vaddr, target));
        }
        unreachable!("page-table unmapping exceeded the tree depth")
    }

    #[inline(always)]
    pub fn unmap_4k(&self, vaddr: VirtAddr) -> UnmapEntryResult<A> {
        self.unmap_at(vaddr, Self::SMALL)
    }

    pub fn unmap_2m(&self, vaddr: VirtAddr) -> UnmapEntryResult<A> {
        self.unmap_at(vaddr, Self::LARGE)
    }

    /// Splits a huge leaf while preserving its mappings. New pages are prepared
    /// privately; the content guard covers publication and flushing.
    /// `vaddr` may be any address within the selected mapping.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split(
        &self,
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

    /// Replaces permission flags for exactly one target-sized page, splitting
    /// a larger leaf if needed. Frame, tags, PAT and A/D history are retained.
    /// A finer subtree is reported rather than overwritten.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    #[inline(always)]
    pub fn mprotect(
        &self,
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
        if target == Self::SMALL {
            return self.protect_4k(vaddr, A::filter_flags(flags), all_cpus);
        }
        self.edit_leaf(vaddr, target, LeafUpdate::Protect(flags), all_cpus)
    }

    #[inline(always)]
    fn protect_4k(
        &self,
        vaddr: VirtAddr,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.edit_leaf(vaddr, Self::SMALL, LeafUpdate::Protect(flags), all_cpus);
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        let current = mapping.entry().load();
        if !current.is_leaf(Self::SMALL) {
            return Err(PagingError::NotMapped);
        }
        // SAFETY: the slot is pinned at Level0 and the content guard excludes writers.
        Ok(unsafe {
            PTPage::<A, P>::protect_leaf(mapping.entry(), current, Self::SMALL, vaddr, flags)
        })
    }

    /// Protects a page-aligned range with per-entry effects, not a transaction.
    /// On error, the returned obligation covers any unflushed prefix edits.
    /// Each table page is locked only while its affected entries are updated.
    /// `all_cpus` selects its scope as in [`Self::split`].
    pub fn mprotect_range(
        &self,
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
        if start == end {
            return (Ok(()), flush);
        }
        self.protect_leaf_range_locked(start.bits(), end.bits(), A::filter_flags(flags), all_cpus)
    }

    fn protect_leaf_range_locked(
        &self,
        start: usize,
        end: usize,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<A::TlbFlushTok>) {
        let mut cursor = start;
        let mut flush = Some(MayNeedFlush::none());
        let mut retries_left = L::LEVEL.depth();
        let mut splits_left = 2;
        loop {
            let mut locked_page = None;
            let mut guard: Option<W::Guard<'_>> = None;
            let result = PTPage::<A, P>::sweep_range(
                &self.root_view(),
                cursor,
                end,
                &mut |page, slot, _, level, entry_start, entry_end| {
                    if locked_page != Some(page) {
                        guard = None;
                        guard = Some(self.wperms.lock(page));
                        locked_page = Some(page);
                    }
                    let current = slot.load();
                    if current.is_table(level) {
                        return Err(RangeUpdateError::Retry);
                    }
                    if !current.is_leaf(level) {
                        return Err(RangeUpdateError::Paging(PagingError::NotMapped));
                    }
                    let leaf_start = entry_start & !(level.size() - 1);
                    if entry_start != leaf_start {
                        return Err(RangeUpdateError::Split(entry_start));
                    }
                    if entry_end != leaf_start.saturating_add(level.size()) {
                        return Err(RangeUpdateError::Split(entry_end - Self::SMALL.size()));
                    }
                    let desired = current.with_leaf_flags(level, flags);
                    if desired.raw() != current.raw() {
                        slot.update_preserving_ad(current, desired);
                        let pending = MayNeedFlush::new(VirtAddr::from(entry_start), level);
                        flush = Some(flush.take().unwrap().and(pending));
                    }
                    Ok(())
                },
            );
            drop(guard);
            match result {
                Ok(_) => return (Ok(()), flush.take().unwrap()),
                Err((retry, RangeUpdateError::Retry)) => {
                    if retries_left == 0 {
                        unreachable!("page-table range update exceeded its retry bound");
                    }
                    retries_left -= 1;
                    cursor = retry;
                }
                Err((retry, RangeUpdateError::Split(split_address))) => {
                    if splits_left == 0 {
                        unreachable!("page-table range update exceeded its boundary split bound");
                    }
                    splits_left -= 1;
                    match self.edit_leaf(
                        VirtAddr::from(split_address),
                        Self::SMALL,
                        LeafUpdate::Protect(flags),
                        all_cpus,
                    ) {
                        Ok(pending) => {
                            flush = Some(flush.take().unwrap().and(pending));
                            cursor = retry;
                        }
                        Err(error) => return (Err(error), flush.take().unwrap()),
                    }
                }
                Err((_, RangeUpdateError::Paging(error))) => {
                    return (Err(error), flush.take().unwrap())
                }
            }
        }
    }

    /// Retags one smallest page, splitting if needed. `all_cpus` selects the
    /// synchronous flush scope as in [`Self::split`].
    pub fn set_shared_4k(
        &self,
        vaddr: VirtAddr,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.edit_leaf(vaddr, Self::SMALL, LeafUpdate::UpdateEncryption(true), all_cpus)
    }

    /// Retags one smallest page as private. `all_cpus` selects the
    /// synchronous flush scope as in [`Self::split`].
    pub fn set_encrypted_4k(
        &self,
        vaddr: VirtAddr,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.edit_leaf(vaddr, Self::SMALL, LeafUpdate::UpdateEncryption(false), all_cpus)
    }

    fn edit_leaf(
        &self,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.tree.policy().check_address(L::LEVEL, vaddr)?;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        for _ in 0..=L::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            if mapping.entry().load().is_table(mapping.page.level()) {
                continue;
            }
            // SAFETY: this borrow pins the slot and the content guard excludes writers.
            return unsafe {
                PTPage::<A, P>::edit_leaf(
                    mapping.entry(),
                    mapping.page.level(),
                    vaddr,
                    target,
                    update,
                    all_cpus,
                )
            };
        }
        unreachable!("page-table update exceeded the tree depth")
    }

    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let view = self.root_view();
        let entry = view.load(idx);
        entry.is_table(view.level()).then(|| PhysAddr::from(entry.address()))
    }

    pub fn map_region_4k(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_region_at(start, end, phys, Self::SMALL, flags, shared)
    }

    pub fn map_region_2m(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_region_at(start, end, phys, Self::LARGE, flags, shared)
    }

    /// Range operations are per-entry, not transactions. Deterministic
    /// whole-range outcomes require caller exclusion of overlapping writers.
    pub fn map_region_at(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        assert!(start <= end && start.is_aligned(target.size()) && end.is_aligned(target.size()));
        let mut vaddr = start;
        while vaddr < end {
            self.map(vaddr, phys + (vaddr - start), target, flags, shared)?;
            vaddr = vaddr + target.size();
        }
        Ok(())
    }

    pub fn map_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        self.map_region_inner(start, end, phys, flags, false)
    }

    /// Skips existing translations only when they already match `phys`.
    pub fn map_region_if_absent(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        self.map_region_inner(start, end, phys, flags, true)
    }

    fn map_region_inner(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: A::PTFlags,
        skip_matching: bool,
    ) -> Result<(), PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        assert!(
            start <= end
                && start.is_aligned(Self::SMALL.size())
                && end.is_aligned(Self::SMALL.size())
        );
        let mut vaddr = start;
        while vaddr < end {
            let paddr = phys + (vaddr - start);
            let mut target = if vaddr.is_aligned(Self::LARGE.size())
                && paddr.is_aligned(Self::LARGE.size())
                && end - vaddr >= Self::LARGE.size()
                && Self::LARGE <= L::LEVEL
            {
                Self::LARGE
            } else {
                Self::SMALL
            };
            let mut result = self.map(vaddr, paddr, target, flags, false);
            if result == Err(PagingError::NotLeafEntry) && target == Self::LARGE {
                target = Self::SMALL;
                result = self.map(vaddr, paddr, target, flags, false);
            }
            match result {
                Ok(()) => vaddr = vaddr + target.size(),
                Err(PagingError::EntryAlreadyPresent { frame, level })
                    if skip_matching && frame == paddr =>
                {
                    vaddr = next_boundary(vaddr, level, end);
                }
                Err(err) => return Err(err),
            }
        }
        Ok(())
    }

    pub fn unmap_region_4k(
        &self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.unmap_region_at(start, end, Self::SMALL)
    }

    pub fn unmap_region_2m(
        &self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        self.unmap_region_at(start, end, Self::LARGE)
    }

    pub fn unmap_region_at(
        &self,
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
        let mut flush = MayNeedFlush::none();
        let mut vaddr = start;
        while vaddr < end {
            let (_, pending) = self.unmap_at_inner(vaddr, target);
            flush = flush.and(pending);
            vaddr = vaddr + target.size();
        }
        Ok(flush)
    }

    /// Clears all leaves encountered in `[start, end)`, including a whole
    /// huge leaf if either boundary falls inside it, as `pagetable` does.
    pub fn unmap_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(bool, MayNeedFlush<A::TlbFlushTok>), PagingError> {
        self.tree.policy().check_range(L::LEVEL, start, end)?;
        assert!(start <= end);
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

    /// Frees empty tables on one path, never the root.
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_addr(&mut self, vaddr: VirtAddr) -> usize {
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, L::LEVEL)) {
            return 0;
        }
        // SAFETY: borrowing excludes local walkers; the caller supplies
        // exclusive ownership and hardware exclusion.
        unsafe { reclaim_path(&self.root_view(), vaddr, |entry| entry.is_clear()) }
    }

    /// Frees empty tables intersecting the half-open range, never the root.
    /// # Safety
    /// As in [`Self::free_page_table_by_addr`], for the entire affected subtree.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        assert!(start <= end);
        if start < end {
            let span = L::LEVEL.size() * PTPage::<A, P>::COUNT;
            let first = start.bits() & (span - 1);
            let last = ((end.bits() - 1) & (span - 1)) + 1;
            assert!(first < last, "range wraps the root's address space");
            // SAFETY: the caller supplies exclusive ownership and excludes all walkers.
            unsafe {
                reclaim_range(
                    &self.root_view(),
                    first,
                    last,
                    |index| self.tree.policy().owns_top_entry(index),
                    |entry| entry.is_clear(),
                )
            };
        }
    }

    /// Frees owned subtrees, retaining borrowed root entries and all data frames.
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

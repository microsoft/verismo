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
use crate::structs::frame::PhysFrame;
use crate::structs::level::{LevelSpec, Lvl, PageLevel};
use crate::structs::mapping::UnmapEntryResult;
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy, UserPolicy};
use crate::structs::ptpage::{
    free_children, reclaim_path, reclaim_range, FlushFootprint, PTPage, PTPagePointer, PTPageTree,
    Translation,
};
use crate::structs::sizes::{
    entry_index, next_boundary, page_level_for_size, PageSize, Size2MiB, Size4KiB, PT_ENTRY_COUNT,
};
use crate::structs::tlb::MayNeedFlush;

#[derive(Clone, Copy)]
struct RangeMapSpec<Arch: ArchPagingMeta> {
    region_start: VirtAddr,
    phys: PhysAddr,
    flags: Arch::PTFlags,
}

struct RangeUnmapState<'a> {
    all_mapped: &'a mut bool,
    footprint: &'a mut FlushFootprint,
}

/// Arch write-permission lock keyed by physical table page. Keys may share one lock or
/// select per-page/striped locks; paging never holds two guards at once.
/// Guards borrow protected metadata/permissions, never live PTE storage.
///
/// # Safety
/// Guards for the same page must exclude each other, acquiring on `lock` and
/// releasing on drop without panicking. Keys and exclusion must remain stable
/// across every tree sharing those pages, including during unwinding.
pub unsafe trait LockSpec<T> {
    /// Arch borrowed guard excluding writers for one keyed table page.
    type Guard<'a>: Deref<Target = T> + DerefMut
    where
        Self: 'a,
        T: 'a;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_>;
}

/// An atomic observation, not a reference to a live entry or a pinned frame.
/// Another update can invalidate its translation immediately.
pub struct MappingSnapshot<Arch: ArchPagingMeta> {
    entry: PTEntry<Arch>,
    level: PageLevel,
}

/// Internal outcome used to restart a range walk after a concurrent split.
enum RangeUpdateError {
    Retry,
    Split(usize, PageLevel),
    Paging(PagingError),
}

impl<Arch: ArchPagingMeta> MappingSnapshot<Arch> {
    pub fn read(&self) -> PTEntry<Arch> {
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
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP,
    T = (),
    Owned: PagingOwnershipPolicy = KernelPolicy,
> {
    tree: PTPageTree<Arch, Alloc, MaxLevel, Owned>,
    wperms: WP,
    marker: PhantomData<T>,
}

/// Arch concurrent kernel page table using `WP` as its PTE write-permission domain.
pub type KernelPageTable<Arch, Alloc, MaxLevel, WP, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, KernelPolicy>;
/// Arch concurrent user page table borrowing the configured kernel root slots.
pub type UserPageTable<
    'kernel,
    Arch,
    Alloc,
    MaxLevel,
    WP,
    const START: usize,
    const END: usize,
    T = (),
> = PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, START, END>>;

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: DirectMappedAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(wperms: WP, flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let root_pa = PTPage::<Arch, Alloc>::new_direct_mapped(MaxLevel::LEVEL, flags)?;
        // SAFETY: construction produced a validated, exclusively owned, unpublished tree.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }
}

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
{
    /// Validates an existing root before constructing its controller.
    /// Rejection or validation unwinding leaves the root allocated.
    /// # Safety
    /// Keep the initialized, correctly leveled, acyclic tree at clean `root_pa`
    /// accessible and aligned for `PTPage` for this controller's lifetime.
    /// Every software user must follow this atomic-access, content-lock and
    /// lifetime protocol. Shared pages must
    /// appear at identical virtual prefixes, never at different aliases.
    /// Without `use_ad`, import presets Arch/D throughout the tree. Exclude all
    /// software and hardware access, and end conflicting Rust references through aliases;
    /// invalidate cached translations and paging structures before resuming use.
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(wperms: WP, root_pa: PhysAddr) -> Result<Self, PagingError> {
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(root_pa, MaxLevel::LEVEL, |slot| {
                PTEntryRef::from_raw(slot.cast_mut()).load()
            })
        }?;
        #[cfg(not(feature = "use_ad"))]
        // SAFETY: validation established shape; the caller excludes all users during import.
        unsafe {
            PTPage::<Arch, Alloc>::normalize_ad_tree(root_pa, MaxLevel::LEVEL);
        }
        // SAFETY: validation establishes shape; ownership and quiescence are the caller's duty.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }

    /// Borrows existing subtrees at `START..END`; the entire range becomes immutable.
    /// Initialize shared root slots before copying if later growth must be visible.
    /// # Safety
    /// `Alloc` must resolve shared physical addresses to the same table pages as `other`.
    /// Shared pages must outlive both trees at identical virtual prefixes,
    /// use the same content-lock domain, and not be reclaimed while in use.
    pub unsafe fn new_from_sharing_top<'kernel, const START: usize, const END: usize>(
        wperms: WP,
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, Arch, Alloc, MaxLevel, WP, START, END, T>, PagingError> {
        let policy = UserPolicy::<START, END>::new();
        let mut tree = PTPageTree::new_root(policy)?;
        {
            // SAFETY: the fresh destination has no software or hardware users.
            let page = unsafe { tree.page_mut() };
            for idx in START..END {
                let entry = other.root_view().load(idx);
                if entry.is_table(MaxLevel::LEVEL) {
                    *page.entry_mut(idx) = entry.for_publication();
                }
            }
        }
        let this = PageTable { tree, wperms, marker: PhantomData };
        this.validate_page_table()?;
        Ok(this)
    }

    /// Gives up the tree and returns its root and content-lock domain.
    /// Arch borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> (WP, PhysAddr) {
        let (wperms, _, root_pa) = self.leak_parts();
        (wperms, root_pa)
    }

    /// Installs an owned subtree in an absent root slot.
    /// # Safety
    /// The subtree must be initialized, correctly leveled, acyclic, mapped and
    /// allocated by this controller's allocator.
    /// Arch new installation transfers its ownership; no other parent may link to it.
    /// Without `use_ad`, new subtrees must be quiesced while their Arch/D bits are
    /// preset; invalidate any cached state before hardware can use them.
    pub unsafe fn populate(
        &mut self,
        idx: usize,
        subpage_pa: PhysAddr,
    ) -> Result<bool, PagingError> {
        if MaxLevel::LEVEL.is_leaf() {
            return Err(PagingError::InvalidLevel);
        }
        let desired = PTEntry::new_table(
            Arch::make_private_address(subpage_pa),
            Arch::PTFlags::parent_flags(),
        );
        let slot = self.root_view().entry(idx);
        let _guard = self.wperms.lock(self.tree.root_paddr());
        let entry = slot.load();
        if entry.is_table(MaxLevel::LEVEL) && entry.address() == subpage_pa.bits() {
            return Ok(false);
        }
        if entry.is_table(MaxLevel::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level: MaxLevel::LEVEL });
        }
        #[cfg(not(feature = "use_ad"))]
        // SAFETY: a new subtree is correctly leveled and quiesced by the caller.
        unsafe {
            PTPage::<Arch, Alloc>::normalize_ad_tree(subpage_pa, MaxLevel::LEVEL.child().unwrap());
        }
        // Only an absent slot changes; ownership transfers with publication.
        slot.store(desired);
        Ok(true)
    }
}

impl<'kernel, Arch, Alloc, MaxLevel, WP, T, const START: usize, const END: usize>
    PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, START, END>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (WP, UserPolicy<'kernel, START, END>, PhysAddr) {
        self.leak_parts()
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
    const SMALL: PageLevel = PageLevel::Level0;
    const LARGE: PageLevel = PageLevel::Level1;

    fn leak_parts(self) -> (WP, Owned, PhysAddr) {
        let (policy, root_pa) = self.tree.into_parts();
        (self.wperms, policy, root_pa)
    }

    pub fn policy(&self) -> &Owned {
        self.tree.policy()
    }

    pub fn owns_top_entry(&self, index: usize) -> bool {
        self.tree.policy().owns_top_entry(index)
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    fn root_view(&self) -> PTPagePointer<'_, Arch, Alloc> {
        self.tree.root()
    }

    /// Arch leaf/absent-entry snapshot. It holds no content lock and gives no
    /// authority to dereference or free the translated data frame.
    #[inline(always)]
    pub fn walk(&self, vaddr: VirtAddr) -> MappingSnapshot<Arch> {
        let position = self.tree.walk(vaddr);
        MappingSnapshot { entry: position.observed, level: position.page.level() }
    }

    /// Installs a leaf, publishing a fully initialized private path when one is absent.
    fn do_map<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let paddr = frame.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        assert!(flags.present());
        let flags = Arch::filter_flags(flags);
        let parent_flags = Arch::filter_flags(parent_flags);
        let addr = if shared {
            Arch::make_shared_address(paddr)
        } else {
            Arch::make_private_address(paddr)
        };
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        let leaf = PTEntry::new(addr, flags);
        let mut mapping = self.root_view().walk(vaddr);
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let level = mapping.page.level();
            if level < target {
                return Err(PagingError::NotLeafEntry);
            }
            if level == target {
                return self.install_leaf(&mapping.page, mapping.index, leaf);
            }
            if mapping.observed.is_table(level) {
                mapping = mapping.page.walk(vaddr);
                continue;
            }
            if mapping.observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            }
            if self.alloc_and_install_leaf(
                &mapping.page,
                mapping.index,
                vaddr,
                target,
                parent_flags,
                leaf,
            )? {
                return Ok(());
            }
            mapping = mapping.page.walk(vaddr);
        }
        unreachable!("mapping traversal exceeded the page-table depth")
    }

    fn install_leaf(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
        index: usize,
        leaf: PTEntry<Arch>,
    ) -> Result<(), PagingError> {
        let level = page.level();
        let _guard = self.wperms.lock(page.paddr());
        let slot = page.entry(index);
        let entry = slot.load();
        if entry.is_table(level) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        slot.store(leaf);
        Ok(())
    }

    fn alloc_and_install_leaf(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
        index: usize,
        vaddr: VirtAddr,
        target: PageLevel,
        parent_flags: Arch::PTFlags,
        leaf: PTEntry<Arch>,
    ) -> Result<bool, PagingError> {
        let child_level = page.level().child().unwrap();
        let mut prepared = PTPageTree::<Arch, Alloc>::new(child_level)?;
        prepared.grow(vaddr, target, parent_flags)?;
        let prepared_mapping = prepared.root().walk(vaddr);
        debug_assert_eq!(prepared_mapping.page.level(), target);
        prepared_mapping.entry().store(leaf);

        let _guard = self.wperms.lock(page.paddr());
        let slot = page.entry(index);
        let current = slot.load();
        if current.is_table(page.level()) {
            return Ok(false);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: page.level() });
        }
        slot.store(PTEntry::new_table(
            Arch::make_private_address(prepared.root_paddr()),
            parent_flags,
        ));
        prepared.release();
        Ok(true)
    }

    #[inline(always)]
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<Arch>, PagingError> {
        let snapshot = self.walk(vaddr);
        // Keep the common 4 KiB translation path free of dynamic level-size dispatch.
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

    /// Checks self-mappings using atomic observations. Arch whole-tree result
    /// requires the caller to exclude concurrent content updates.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        // SAFETY: this borrow pins every followed table; all observations are atomic.
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(self.tree.root_paddr(), MaxLevel::LEVEL, |slot| {
                PTEntryRef::from_raw(slot.cast_mut()).load()
            })
        }
    }

    fn map_range_leaf(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        match target {
            PageLevel::Level0 => self.do_map(
                Page::<Size4KiB>::from_start_address(vaddr)
                    .map_err(|_| PagingError::InvalidAddress)?,
                PhysFrame::<Size4KiB>::from_start_address(paddr)
                    .map_err(|_| PagingError::InvalidAddress)?,
                flags,
                shared,
                parent_flags,
            ),
            PageLevel::Level1 => self.do_map(
                Page::<Size2MiB>::from_start_address(vaddr)
                    .map_err(|_| PagingError::InvalidAddress)?,
                PhysFrame::<Size2MiB>::from_start_address(paddr)
                    .map_err(|_| PagingError::InvalidAddress)?,
                flags,
                shared,
                parent_flags,
            ),
            _ => Err(PagingError::InvalidLevel),
        }
    }

    fn check_map_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        self.tree.policy().check_range(MaxLevel::LEVEL, start, end)?;
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        if !phys.is_aligned(Self::SMALL.size()) {
            return Err(PagingError::InvalidAddress);
        }
        if !start.is_aligned(Self::SMALL.size()) || !end.is_aligned(Self::SMALL.size()) {
            return Err(PagingError::InvalidRange);
        }
        if start < end && phys.checked_add((end - start) - Self::SMALL.size()).is_none() {
            return Err(PagingError::InvalidRange);
        }
        Ok(())
    }

    fn region_paddr(spec: RangeMapSpec<Arch>, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        spec.phys.checked_add(vaddr - spec.region_start).ok_or(PagingError::InvalidRange)
    }

    fn region_target(&self, vaddr: VirtAddr, end: VirtAddr, paddr: PhysAddr) -> PageLevel {
        if Self::LARGE <= MaxLevel::LEVEL
            && vaddr.is_aligned(Self::LARGE.size())
            && paddr.is_aligned(Self::LARGE.size())
            && end - vaddr >= Self::LARGE.size()
        {
            Self::LARGE
        } else {
            Self::SMALL
        }
    }

    fn leaf_entry(paddr: PhysAddr, target: PageLevel, flags: Arch::PTFlags) -> PTEntry<Arch> {
        let addr = Arch::make_private_address(paddr);
        let flags = Arch::filter_flags(flags);
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        PTEntry::new(addr, flags)
    }

    fn map_leaf_run(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        target: PageLevel,
        spec: RangeMapSpec<Arch>,
    ) -> Result<(), PagingError> {
        debug_assert_eq!(page.level(), target);
        let _guard = self.wperms.lock(page.paddr());
        while start < end {
            let index = entry_index(start, target);
            let observed = page.load(index);
            if observed.is_table(target) {
                return Err(PagingError::NotLeafEntry);
            }
            if observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level: target });
            }
            let paddr = Self::region_paddr(spec, start)?;
            page.store(index, Self::leaf_entry(paddr, target, spec.flags));
            start = next_boundary(start, target, end);
        }
        Ok(())
    }

    #[inline(always)]
    fn map_region_child<PL: LevelSpec>(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        spec: RangeMapSpec<Arch>,
    ) -> Result<(), PagingError> {
        match PL::DEPTH {
            1 => self.map_region_level::<Lvl<0>>(page, start, end, spec),
            2 => self.map_region_level::<Lvl<1>>(page, start, end, spec),
            3 => self.map_region_level::<Lvl<2>>(page, start, end, spec),
            4 => self.map_region_level::<Lvl<3>>(page, start, end, spec),
            _ => unreachable!("leaf page has no child"),
        }
    }

    #[inline(always)]
    fn map_region_level<PL: LevelSpec>(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        spec: RangeMapSpec<Arch>,
    ) -> Result<(), PagingError> {
        let level = PL::LEVEL;
        debug_assert_eq!(page.level(), level);
        if PL::DEPTH == 0 {
            return self.map_leaf_run(&page, start, end, level, spec);
        }

        while start < end {
            let slot_end = next_boundary(start, level, end);
            let paddr = Self::region_paddr(spec, start)?;
            let target = self.region_target(start, slot_end, paddr);
            let index = entry_index(start, level);
            let observed = page.load(index);

            if target == level {
                if observed.is_table(level) {
                    let child = page
                        .child_from_observed(observed)
                        .map_err(|_| PagingError::NotLeafEntry)?;
                    self.map_region_child::<PL>(child, start, slot_end, spec)?;
                } else {
                    match self.map_leaf_run(&page, start, slot_end, level, spec) {
                        Err(PagingError::NotLeafEntry) => {
                            let child = page.child(index).map_err(|_| PagingError::NotLeafEntry)?;
                            self.map_region_child::<PL>(child, start, slot_end, spec)?;
                        }
                        result => result?,
                    }
                }
                start = slot_end;
                continue;
            }

            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                self.map_region_child::<PL>(child, start, slot_end, spec)?;
                start = slot_end;
                continue;
            }
            if observed.present() {
                let guard = self.wperms.lock(page.paddr());
                let current = page.load(index);
                if current.is_table(level) {
                    let child =
                        page.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry)?;
                    drop(guard);
                    self.map_region_child::<PL>(child, start, slot_end, spec)?;
                    start = slot_end;
                    continue;
                }
                if current.present() {
                    return Err(PagingError::EntryAlreadyPresent { level });
                }
                drop(guard);
            }

            self.map_range_leaf(
                start,
                paddr,
                target,
                spec.flags,
                false,
                Arch::PTFlags::parent_flags(),
            )?;
            let next = next_boundary(start, target, slot_end);
            if next < slot_end {
                let child = page.child(index).map_err(|_| PagingError::NotLeafEntry)?;
                self.map_region_child::<PL>(child, next, slot_end, spec)?;
            }
            start = slot_end;
        }
        Ok(())
    }

    fn map_region_sweep(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        spec: RangeMapSpec<Arch>,
    ) -> Result<(), PagingError> {
        if start == end {
            return Ok(());
        }
        let root = self.root_view();
        match MaxLevel::LEVEL {
            PageLevel::Level0 => self.map_region_level::<Lvl<0>>(root, start, end, spec),
            PageLevel::Level1 => self.map_region_level::<Lvl<1>>(root, start, end, spec),
            PageLevel::Level2 => self.map_region_level::<Lvl<2>>(root, start, end, spec),
            PageLevel::Level3 => self.map_region_level::<Lvl<3>>(root, start, end, spec),
            PageLevel::Level4 => self.map_region_level::<Lvl<4>>(root, start, end, spec),
        }
    }

    #[inline(always)]
    fn unmap_region_l0(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        debug_assert_eq!(page.level(), PageLevel::Level0);
        let page_paddr = page.paddr();
        while start < end {
            let _guard = self.wperms.lock(page_paddr);
            let slot = page.entry(entry_index(start, PageLevel::Level0));
            if slot.load().is_leaf(PageLevel::Level0) {
                slot.swap(PTEntry::empty());
                state.footprint.include(start, PageLevel::Level0);
            } else {
                *state.all_mapped = false;
            }
            start = next_boundary(start, PageLevel::Level0, end);
        }
        Ok(())
    }

    #[inline(always)]
    fn unmap_region_level<const LEVEL: usize>(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
        mut lower: impl for<'tree> FnMut(
            &Self,
            PTPagePointer<'tree, Arch, Alloc>,
            VirtAddr,
            VirtAddr,
            &mut RangeUnmapState<'_>,
        ) -> Result<(), PagingError>,
    ) -> Result<(), PagingError> {
        let level = PageLevel::at::<LEVEL>();
        debug_assert!(LEVEL > 0);
        debug_assert_eq!(page.level(), level);
        let page_paddr = page.paddr();
        while start < end {
            let slot_end = next_boundary(start, level, end);
            let index = entry_index(start, level);
            let slot = page.entry(index);
            let mut observed = slot.load();
            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                lower(self, child, start, slot_end, state)?;
                start = slot_end;
                continue;
            }
            let guard = self.wperms.lock(page_paddr);
            observed = slot.load();
            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                drop(guard);
                lower(self, child, start, slot_end, state)?;
                start = slot_end;
                continue;
            }
            if !observed.is_leaf(level) {
                drop(guard);
                *state.all_mapped = false;
                start = slot_end;
                continue;
            }
            if start.is_aligned(level.size()) && end - start >= level.size() {
                slot.swap(PTEntry::empty());
                drop(guard);
                state.footprint.include(start, level);
                start = slot_end;
                continue;
            }

            let target = level.child().unwrap();
            // SAFETY: the content guard pins the slot and excludes competing writers.
            let _ = unsafe { PTPage::<Arch, Alloc>::split_leaf(slot, level, start, target, true) }?;
            let child = page.child(index).map_err(|_| PagingError::NotLeafEntry)?;
            drop(guard);
            lower(self, child, start, slot_end, state)?;
            start = slot_end;
        }
        Ok(())
    }

    #[inline(always)]
    fn unmap_region_l1(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        self.unmap_region_level::<1>(page, start, end, state, Self::unmap_region_l0)
    }

    #[inline(always)]
    fn unmap_region_l2(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        self.unmap_region_level::<2>(page, start, end, state, Self::unmap_region_l1)
    }

    #[inline(always)]
    fn unmap_region_l3(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        self.unmap_region_level::<3>(page, start, end, state, Self::unmap_region_l2)
    }

    #[inline(always)]
    fn unmap_region_l4(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        self.unmap_region_level::<4>(page, start, end, state, Self::unmap_region_l3)
    }

    fn unmap_region_sweep(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        if start == end {
            return Ok(());
        }
        let root = self.root_view();
        match MaxLevel::LEVEL {
            PageLevel::Level0 => self.unmap_region_l0(root, start, end, state),
            PageLevel::Level1 => self.unmap_region_l1(root, start, end, state),
            PageLevel::Level2 => self.unmap_region_l2(root, start, end, state),
            PageLevel::Level3 => self.unmap_region_l3(root, start, end, state),
            PageLevel::Level4 => self.unmap_region_l4(root, start, end, state),
        }
    }

    /// Maps `page` to the matching physical `frame`, building intermediate
    /// tables with `parent_flags`. Existing mappings are never overwritten.
    pub fn map_with_parent_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        self.do_map(page, frame, flags, shared, parent_flags)
    }

    /// [`Self::map_with_parent_flags`] with the architecture's default flags
    /// for intermediate tables.
    pub fn map<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_with_parent_flags(page, frame, flags, shared, Arch::PTFlags::parent_flags())
    }

    /// Removes the mapping of `page`, splitting a larger leaf first if needed.
    /// Arch mapping already represented by smaller leaves is not coalesced.
    /// `all_cpus` selects the synchronous flush scope for any split.
    #[inline(always)]
    pub fn unmap<PS: PageSize>(&self, page: Page<PS>, all_cpus: bool) -> UnmapEntryResult<Arch> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        if target == Self::SMALL {
            return self.unmap_4k_inner(vaddr, all_cpus);
        }
        self.unmap_with_split(vaddr, target, all_cpus)
    }

    #[inline(always)]
    fn unmap_4k_inner(&self, vaddr: VirtAddr, all_cpus: bool) -> UnmapEntryResult<Arch> {
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.unmap_with_split(vaddr, Self::SMALL, all_cpus);
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        if !mapping.entry().load().is_leaf(Self::SMALL) {
            return Ok((None, MayNeedFlush::none()));
        }
        let entry = mapping.entry().swap(PTEntry::empty());
        Ok((Some(entry), MayNeedFlush::new_4k(vaddr)))
    }

    fn unmap_with_split(
        &self,
        vaddr: VirtAddr,
        target: PageLevel,
        all_cpus: bool,
    ) -> UnmapEntryResult<Arch> {
        let mut flush = MayNeedFlush::none();
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            let entry = mapping.entry().load();
            if entry.is_table(mapping.page.level()) {
                continue;
            }
            if !entry.is_leaf(mapping.page.level()) {
                return Ok((None, flush));
            }
            if mapping.page.level() == target {
                let entry = mapping.entry().swap(PTEntry::empty());
                let pending = if target == Self::SMALL {
                    MayNeedFlush::new_4k(vaddr)
                } else {
                    MayNeedFlush::new(vaddr, target)
                };
                return Ok((Some(entry), flush.and(pending)));
            }
            drop(_guard);
            flush = flush.and(self.split(vaddr, target, all_cpus)?);
        }
        unreachable!("unmap traversal exceeded the page-table depth")
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
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        match self.with_locked_leaf(vaddr, target, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::split_leaf(entry, level, vaddr, target, all_cpus)
        }) {
            Ok(flush) => Ok(flush),
            Err(PagingError::NotLeafEntry) => Ok(MayNeedFlush::none()),
            Err(err) => Err(err),
        }
    }

    /// Replaces flags for exactly one typed page, splitting
    /// a larger leaf if needed. Frame, tags, PAT and Arch/D history are retained.
    /// Arch finer subtree is reported rather than overwritten.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    #[inline(always)]
    pub fn set_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        if target == Self::SMALL {
            self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
            return self.set_flags_4k(vaddr, Arch::filter_flags(flags), all_cpus);
        }
        self.with_locked_leaf(vaddr, target, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_at(
                entry, level, vaddr, target, flags, all_cpus,
            )
        })
    }

    #[inline(always)]
    fn set_flags_4k(
        &self,
        vaddr: VirtAddr,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.with_locked_leaf(vaddr, Self::SMALL, |entry, level| unsafe {
                PTPage::<Arch, Alloc>::update_leaf_flags_at(
                    entry,
                    level,
                    vaddr,
                    Self::SMALL,
                    flags,
                    all_cpus,
                )
            });
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        let current = mapping.entry().load();
        if !current.is_leaf(Self::SMALL) {
            return Err(PagingError::NotMapped);
        }
        // SAFETY: the slot is pinned at Level0 and the content guard excludes writers.
        Ok(unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_in_place(
                mapping.entry(),
                current,
                Self::SMALL,
                vaddr,
                flags,
            )
        })
    }

    /// Replaces flags across a page-aligned range with per-entry effects, not a transaction.
    /// On error, the returned obligation covers any unflushed prefix edits.
    /// Each table page is locked only while its affected entries are updated.
    /// `all_cpus` selects its scope as in [`Self::split`].
    pub fn set_flags_range(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<Arch::TlbFlushTok>) {
        let flush = MayNeedFlush::none();
        if let Err(error) = self.tree.policy().check_range(MaxLevel::LEVEL, start, end) {
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
        self.set_flags_range_inner(start.bits(), end.bits(), Arch::filter_flags(flags), all_cpus)
    }

    fn set_flags_range_inner(
        &self,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<Arch::TlbFlushTok>) {
        let mut cursor = start;
        let mut flush = MayNeedFlush::none();
        let mut footprint = FlushFootprint::default();
        let mut retries_left = MaxLevel::LEVEL.depth();
        let mut retry_cursor = cursor;
        let mut boundary_splits_left = 2;
        loop {
            if cursor != retry_cursor {
                retry_cursor = cursor;
                retries_left = MaxLevel::LEVEL.depth();
            }
            let mapping = self.root_view().walk(VirtAddr::from(cursor));
            if mapping.page.level() == Self::SMALL {
                let page = mapping.page_paddr();
                let _guard = self.wperms.lock(page);
                let run_start = cursor;
                let count =
                    ((end - cursor) / Self::SMALL.size()).min(PT_ENTRY_COUNT - mapping.index);
                let mut changed = false;
                for index in mapping.index..mapping.index + count {
                    let slot = mapping.page.entry(index);
                    let current = slot.load();
                    if !current.is_leaf(Self::SMALL) {
                        if changed {
                            footprint.include(VirtAddr::from(run_start), Self::SMALL);
                            footprint.include(
                                VirtAddr::from(
                                    run_start + (index - mapping.index - 1) * Self::SMALL.size(),
                                ),
                                Self::SMALL,
                            );
                        }
                        let pending = flush.and(footprint.token());
                        return (Err(PagingError::NotMapped), pending);
                    }
                    let mut desired = current;
                    PTPage::<Arch, Alloc>::set_leaf_flags(&mut desired, flags);
                    if desired.raw() != current.raw() {
                        slot.update_preserving_ad(current, desired);
                        changed = true;
                    }
                }
                cursor += count * Self::SMALL.size();
                if changed {
                    footprint.include(VirtAddr::from(run_start), Self::SMALL);
                    footprint.include(VirtAddr::from(cursor - Self::SMALL.size()), Self::SMALL);
                }
                // Crossing the canonical gap wraps the low segment into its high alias.
                cursor = VirtAddr::from(cursor).bits();
                if cursor == end {
                    let pending = flush.and(footprint.token());
                    return (Ok(()), pending);
                }
                continue;
            }

            let mut locked_page = None;
            let mut guard: Option<WP::Guard<'_>> = None;
            let result = PTPage::<Arch, Alloc>::sweep_range(
                &self.root_view(),
                cursor,
                end,
                &mut |page, slot, observed, level, entry_start, entry_end| {
                    let current = if locked_page != Some(page) {
                        guard = None;
                        guard = Some(self.wperms.lock(page));
                        locked_page = Some(page);
                        slot.load()
                    } else {
                        observed
                    };
                    if current.is_table(level) {
                        return Err(RangeUpdateError::Retry);
                    }
                    if !current.is_leaf(level) {
                        return Err(RangeUpdateError::Paging(PagingError::NotMapped));
                    }
                    let leaf_start = entry_start & !(level.size() - 1);
                    if entry_start != leaf_start {
                        return Err(RangeUpdateError::Split(
                            entry_start,
                            Self::largest_covered_level(entry_start, entry_end, level, false),
                        ));
                    }
                    if entry_end != leaf_start.saturating_add(level.size()) {
                        let target =
                            Self::largest_covered_level(entry_start, entry_end, level, true);
                        return Err(RangeUpdateError::Split(entry_end - target.size(), target));
                    }
                    let mut desired = current;
                    PTPage::<Arch, Alloc>::set_leaf_flags(&mut desired, flags);
                    if desired.raw() != current.raw() {
                        slot.update_preserving_ad(current, desired);
                        footprint.include(VirtAddr::from(entry_start), level);
                    }
                    Ok(())
                },
            );
            drop(guard);
            match result {
                Ok(_) => {
                    let pending = flush.and(footprint.token());
                    return (Ok(()), pending);
                }
                Err((retry, RangeUpdateError::Retry)) => {
                    if retries_left == 0 {
                        unreachable!("page-table range update exceeded its retry bound");
                    }
                    retries_left -= 1;
                    cursor = retry;
                }
                Err((retry, RangeUpdateError::Split(split_address, target))) => {
                    if boundary_splits_left == 0 {
                        unreachable!("page-table range update exceeded its boundary split bound");
                    }
                    boundary_splits_left -= 1;
                    let split_address = VirtAddr::from(split_address);
                    match self.with_locked_leaf(split_address, target, |entry, level| unsafe {
                        PTPage::<Arch, Alloc>::update_leaf_flags_at(
                            entry,
                            level,
                            split_address,
                            target,
                            flags,
                            all_cpus,
                        )
                    }) {
                        Ok(pending) => {
                            flush = flush.and(pending);
                            cursor = retry;
                        }
                        Err(error) => {
                            let pending = flush.and(footprint.token());
                            return (Err(error), pending);
                        }
                    }
                }

                Err((_, RangeUpdateError::Paging(error))) => {
                    let pending = flush.and(footprint.token());
                    return (Err(error), pending);
                }
            }
        }
    }

    fn largest_covered_level(
        start: usize,
        end: usize,
        level: PageLevel,
        align_end: bool,
    ) -> PageLevel {
        let mut target = level.child().unwrap();
        while target > Self::SMALL
            && (end - start < target.size()
                || if align_end {
                    end & (target.size() - 1) != 0
                } else {
                    start & (target.size() - 1) != 0
                })
        {
            target = target.child().unwrap();
        }
        target
    }

    /// Retags `page` as shared, splitting if needed. `all_cpus` selects the
    /// synchronous flush scope as in [`Self::split`].
    pub fn set_shared<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.with_locked_leaf(vaddr, target, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(
                entry, level, vaddr, target, true, all_cpus,
            )
        })
    }

    /// Retags `page` as private. `all_cpus` selects the
    /// synchronous flush scope as in [`Self::split`].
    pub fn set_private<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.with_locked_leaf(vaddr, target, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(
                entry, level, vaddr, target, false, all_cpus,
            )
        })
    }

    fn with_locked_leaf(
        &self,
        vaddr: VirtAddr,
        target: PageLevel,
        update: impl FnOnce(
            PTEntryRef<'_, Arch>,
            PageLevel,
        ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError>,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            if mapping.entry().load().is_table(mapping.page.level()) {
                continue;
            }
            return update(mapping.entry(), mapping.page.level());
        }
        unreachable!("page-table update exceeded the tree depth")
    }

    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let view = self.root_view();
        let entry = view.load(idx);
        entry.is_table(view.level()).then(|| PhysAddr::from(entry.address()))
    }

    /// Range operations are per-entry, not transactions. Deterministic
    /// whole-range outcomes require caller exclusion of overlapping writers.
    pub fn map_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        phys: PhysAddr,
        flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        self.check_map_region(start, end, phys, flags)?;
        self.map_region_sweep(start, end, RangeMapSpec { region_start: start, phys, flags })
    }

    /// Unmaps `[start, end)` at the largest currently represented leaf sizes.
    /// Partially covered huge leaves are split only as far as the range needs.
    /// Splitting can allocate; an error leaves the successfully processed
    /// prefix unmapped and synchronously flushes it.
    /// Reports whether every smallest page in the range was mapped.
    pub fn unmap_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(bool, MayNeedFlush<Arch::TlbFlushTok>), PagingError> {
        self.tree.policy().check_range(MaxLevel::LEVEL, start, end)?;
        let mut all_mapped = true;
        let mut footprint = FlushFootprint::default();
        let mut state = RangeUnmapState { all_mapped: &mut all_mapped, footprint: &mut footprint };
        if let Err(error) = self.unmap_region_sweep(start, end, &mut state) {
            let flush = footprint.token::<Arch::TlbFlushTok>();
            if flush.is_pending() {
                flush.flush_tlb_global_sync();
            }
            return Err(error);
        }
        Ok((all_mapped, footprint.token::<Arch::TlbFlushTok>()))
    }

    /// Frees empty tables on one path, never the root.
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_addr(&mut self, vaddr: VirtAddr) -> usize {
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, MaxLevel::LEVEL)) {
            return 0;
        }
        // SAFETY: borrowing excludes local walkers; the caller supplies
        // exclusive ownership and hardware exclusion.
        // Arch zero word excludes non-present state retained by concurrent protocols.
        unsafe { reclaim_path(&self.root_view(), vaddr, |entry| entry.is_clear()) }
    }

    /// Frees empty tables intersecting the half-open range, never the root.
    /// # Safety
    /// As in [`Self::free_page_table_by_addr`], for the entire affected subtree.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        assert!(start <= end);
        if start < end {
            let span = MaxLevel::LEVEL.size() * PT_ENTRY_COUNT;
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
                    // Arch zero word excludes non-present state retained by concurrent protocols.
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

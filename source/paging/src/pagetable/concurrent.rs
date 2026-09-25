//! The `pagetable` API with concurrent walks and serialized entry updates.
//! Shared borrows pin table pages; exclusive borrows permit reclamation.
//! External synchronization provides those borrows but does not fence hardware
//! walkers; the embedder supplies synchronous TLB hooks and hardware quiescence.
//!
//! # Public API
//!
//! - Types: [`PageTable`], [`KernelPageTable`], [`UserPageTable`],
//!   [`LockSpec`], [`UnmapEntryResult`], and [`PopulateError`].
//! - Construction and ownership: [`PageTable::new`], [`PageTable::from_root`],
//!   [`PageTable::new_from_sharing_top`], [`PageTable::leak`],
//!   [`PageTable::leak_with_policy`], and [`PageTable::root_paddr`].
//! - Page operations: [`PageTable::walk`], [`PageTable::translate`],
//!   [`PageTable::phys_addr`], [`PageTable::map`],
//!   [`PageTable::map_with_parent_flags`], [`PageTable::unmap`],
//!   [`PageTable::split`], [`PageTable::set_flags`], [`PageTable::set_shared`],
//!   [`PageTable::set_private`], and [`PageTable::next_table_pa`].
//! - Range operations: [`PageTable::map_region`], [`PageTable::unmap_region`],
//!   and [`PageTable::set_flags_range`].
//! - Subtree ownership: [`PageTable::populate_owned`],
//!   [`PageTable::populate_shared`], [`PageTable::free_page_table_by_addr`],
//!   [`PageTable::cleanup_page_tables_by_range`], and
//!   [`PageTable::free_children`].
//! - Validation: [`PageTable::validate_page_table`].

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{
    assert_borrowed_disjoint_from, KernelPolicy, OwnedIndices, PagingOwnershipPolicy, Policy,
    UserPolicy,
};
use crate::structs::ptpage::{
    DetachedPageTable, Live, OwnedSubtree, PTPage, PTPageRef, PTPageTree, Translation, WalkLevel,
    WalkLevelImpl, WalkResult,
};
use crate::structs::sizes::{entry_index, Huge, PageSize, Regular, PT_ENTRY_COUNT};
use crate::structs::tlb::{with_detach_batch, DetachBatch, MayNeedFlush};

const DETACHED_PATH_CAPACITY: usize = 4;

/// A removed entry paired with any TLB invalidation it leaves outstanding.
pub type UnmapEntryResult<A> =
    Result<(Option<PTEntry<A>>, MayNeedFlush<<A as ArchPagingMeta>::TlbFlushTok>), PagingError>;

/// A failed owned-subtree installation that returns the unconsumed subtree.
pub struct PopulateError<S> {
    /// Why the subtree was not installed.
    pub error: PagingError,
    /// The still-unlinked subtree returned to the caller.
    pub subtree: S,
}

fn shared_top_entry<Arch, Alloc, MaxLevel, WP, T, TargetOwned, SourceOwned>(
    idx: usize,
    other: &PageTable<Arch, Alloc, MaxLevel, WP, T, Policy<SourceOwned>>,
) -> Result<PTEntry<Arch>, PagingError>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    TargetOwned: OwnedIndices,
    SourceOwned: OwnedIndices,
{
    assert!(idx < PT_ENTRY_COUNT);
    assert!(!TargetOwned::contains(idx));
    assert!(SourceOwned::contains(idx));
    let entry = other.root_view().load(idx);
    if !entry.present() {
        return Err(PagingError::NotMapped);
    }
    if !entry.is_present_table(MaxLevel::LEVEL) {
        return Err(PagingError::InvalidLevel);
    }
    Ok(entry)
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

    /// Inputs: table address.
    /// Requires: stable lock domain.
    /// Returns: exclusive write guard.
    fn lock(&self, page: PhysAddr) -> Self::Guard<'_>;
}

/// Shared access permits walk, map, unmap and split, but never removes an
/// installed table pointer. Freeing needs `&mut self` and hardware exclusion.
/// Drop frees the root and owned descendant tables, never shared subtrees or data
/// frames. Externally managed or hardware-active trees need `ManuallyDrop` or `leak`.
pub struct PageTable<
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP,
    T = (),
    Owned: PagingOwnershipPolicy = KernelPolicy,
> {
    pub(super) tree: PTPageTree<Arch, Alloc, MaxLevel, Owned, Live>,
    pub(super) wperms: WP,
    marker: PhantomData<T>,
}

/// Arch concurrent kernel page table using `WP` as its PTE write-permission domain.
pub type KernelPageTable<Arch, Alloc, MaxLevel, WP, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, KernelPolicy>;
/// Arch concurrent user page table borrowing the configured kernel root entries.
pub type UserPageTable<Arch, Alloc, MaxLevel, WP, Owned, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<Owned>>;

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: DirectMappedAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(wperms: WP, flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let tree = PTPageTree::new_direct_mapped(flags)?;
        tree.validate()?;
        let tree = tree.into_live();
        Ok(Self { tree, wperms, marker: PhantomData })
    }
}

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
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
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(wperms: WP, root_pa: PhysAddr) -> Result<Self, PagingError> {
        // SAFETY: tree accessibility and ownership are required by this constructor.
        let tree =
            unsafe { PTPageTree::<Arch, Alloc, MaxLevel, KernelPolicy>::from_root(root_pa) }?
                .into_live();
        Ok(Self { tree, wperms, marker: PhantomData })
    }

    /// Borrows the root entries not selected by `Owned`; those entries become
    /// immutable. `wperms` protects only independently owned entries.
    ///
    /// Policies that leave the same index borrowed cannot be shared:
    /// ```compile_fail,E0080
    /// use paging::address::{Address, PhysAddr, VirtAddr};
    /// use paging::level::Lvl;
    /// use paging::os_contract::{PagingAllocator, PagingError};
    /// use paging::pagetable::{KernelPageTable, LockSpec, PageTable};
    /// use paging::policy::{CoveredRange, Policy};
    /// use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};
    /// use std::sync::{Mutex, MutexGuard};
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// struct Platform;
    ///
    /// unsafe impl X86PagingParams for Platform {
    ///     fn private_mask() -> usize { 0 }
    ///     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    ///     fn flush_tlb_global_sync(_: FlushScope) {}
    /// }
    ///
    /// struct Allocator;
    ///
    /// unsafe impl PagingAllocator for Allocator {
    ///     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
    ///         VirtAddr::from(paddr.bits())
    ///     }
    ///     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
    ///         PhysAddr::from(vaddr.bits())
    ///     }
    ///     fn allocate_table_page() -> Result<PhysAddr, PagingError> {
    ///         unreachable!()
    ///     }
    ///     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// }
    ///
    /// struct Locks(Mutex<()>);
    ///
    /// unsafe impl LockSpec<()> for Locks {
    ///     type Guard<'a> = MutexGuard<'a, ()>;
    ///     fn lock(&self, _: PhysAddr) -> Self::Guard<'_> {
    ///         self.0.lock().unwrap()
    ///     }
    /// }
    ///
    /// type Arch = X86Paging<Platform>;
    /// type Source = PageTable<
    ///     Arch, Allocator, Lvl<3>, Locks, (),
    ///     Policy<CoveredRange<0, 256>>,
    /// >;
    ///
    /// fn overlap(source: &Source, locks: Locks) {
    ///     let _ = unsafe {
    ///         KernelPageTable::<Arch, Allocator, Lvl<3>, Locks>::
    ///             new_from_sharing_top::<CoveredRange<0, 256>>(locks, source)
    ///     };
    /// }
    ///
    /// fn main() {
    ///     let source = std::mem::MaybeUninit::<Source>::uninit();
    ///     unsafe {
    ///         overlap(source.assume_init_ref(), Locks(Mutex::new(())));
    ///     }
    /// }
    /// ```
    /// # Safety
    ///
    /// The source page table should not free its PT pages at the MaxLevel - 1,
    /// to ensure that the shared top entries remain valid and will not point to reclaimed pages,
    /// which may poison the page table.
    ///
    /// In a common case, this is called to derive a user page table from a
    /// kernel page table, sharing some top entries. Thus, we just need to
    /// ensure the kernel page table does not free its top-level PT pages before
    /// detaching them from all page tables.
    pub unsafe fn new_from_sharing_top<Owned: OwnedIndices>(
        wperms: WP,
        source: &PageTable<Arch, Alloc, MaxLevel, WP, T, Policy<impl OwnedIndices>>,
    ) -> Result<UserPageTable<Arch, Alloc, MaxLevel, WP, Owned, T>, PagingError> {
        assert_borrowed_disjoint_from::<_, Owned>(source.tree.policy());
        let policy = UserPolicy::<Owned>::new();
        let mut tree = PTPageTree::new_root(policy)?;
        for idx in (0..PT_ENTRY_COUNT).filter(|index| !Owned::contains(*index)) {
            match shared_top_entry::<_, _, _, _, _, Owned, _>(idx, source) {
                Ok(entry) => *tree.root_page_mut().entry_mut(idx) = entry,
                Err(PagingError::NotMapped) => {}
                Err(error) => return Err(error),
            }
        }
        tree.validate()?;
        let tree = tree.into_live();
        Ok(PageTable { tree, wperms, marker: PhantomData })
    }

    /// Gives up the tree and returns its root and content-lock domain.
    /// Arch borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> (WP, PhysAddr) {
        let (wperms, _, root_pa) = self.leak_parts();
        (wperms, root_pa)
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<Owned>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: OwnedIndices,
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak_with_policy(self) -> (WP, UserPolicy<Owned>, PhysAddr) {
        self.leak_parts()
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
    pub(super) const SMALL: PageLevel = PageLevel::Level0;

    /// Inputs: owned controller.
    /// Requires: none.
    /// Returns: lock, policy, and unreclaimed root.
    fn leak_parts(self) -> (WP, Owned, PhysAddr) {
        let (policy, root_pa) = self.tree.into_parts();
        (self.wperms, policy, root_pa)
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    /// Inputs: controller borrow.
    /// Requires: live tree.
    /// Returns: pinned atomic root view.
    pub(super) fn root_view(&self) -> PTPageRef<'_, Arch, Alloc, MaxLevel> {
        self.tree.root()
    }

    /// Arch leaf/absent-entry snapshot. It holds no content lock and gives no
    /// authority to dereference or free the translated data frame.
    #[inline(always)]
    pub fn walk(&self, vaddr: VirtAddr) -> WalkResult<Arch> {
        self.tree.root().walk(vaddr)
    }

    /// Maps `page` to the matching physical `frame`, building intermediate
    /// tables with `parent_flags`. Existing mappings are never overwritten.
    #[inline(always)]
    pub fn map_with_parent_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let paddr = frame.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        // This implementation supports mappings only through the 1 GiB leaf level.
        if target > PageLevel::Level2 || target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        // Mapping a non-present entry would create an inaccessible leaf.
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
        self.map_from(&self.root_view(), page, parent_flags, leaf)
    }

    /// Installs `leaf` below a validated pinned subtree.
    #[inline(always)]
    fn map_from<PS: PageSize, L: WalkLevelImpl>(
        &self,
        table: &PTPageRef<'_, Arch, Alloc, L>,
        page: Page<PS>,
        parent_flags: Arch::PTFlags,
        leaf: PTEntry<Arch>,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let level = L::LEVEL;
        if level < target {
            return Err(PagingError::NotLeafEntry);
        }
        let index = entry_index(vaddr, level);
        let observed = table.load(index);
        if observed.is_present_table(level) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
            return self.map_from(&child, page, parent_flags, leaf);
        }
        if level == target {
            let mut write = table.lock_to_update(&self.wperms);
            let entry = write.load(index);
            if entry.is_table(level) {
                return Err(PagingError::NotLeafEntry);
            }
            if entry.present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            }
            return write.install_leaf(index, leaf);
        }

        if observed.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }

        let mut prepared = PTPageTree::<Arch, Alloc, L::ChildLevel>::new_root(KernelPolicy::new())?;
        prepared.grow(page, parent_flags)?;
        prepared.store_uninstalled(page, leaf)?;

        let mut write = table.lock_to_update(&self.wperms);
        let current = write.load(index);
        if current.is_present_table(level) {
            let child =
                table.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry)?;
            drop(write);
            return self.map_from(&child, page, parent_flags, leaf);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        write.publish_table(
            index,
            PTEntry::new_table(Arch::make_private_address(prepared.root_paddr()), parent_flags),
        )?;
        prepared.release();
        Ok(())
    }

    #[inline(always)]
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<Arch>, PagingError> {
        let snapshot = self.walk(vaddr);
        let level = snapshot.level();
        let entry = snapshot.read();
        // Keep the common 4 KiB translation path free of dynamic level-size dispatch.
        if level == PageLevel::Level0 {
            if !entry.present() {
                return Err(PagingError::NotMapped);
            }
            let offset = vaddr.bits() & (Self::SMALL.size() - 1);
            return Ok(Translation::new(
                PhysAddr::from((entry.paddr_field() & !(Self::SMALL.size() - 1)) + offset),
                level,
            ));
        }
        if !entry.is_present_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (level.size() - 1);
        Ok(Translation::new(
            PhysAddr::from((entry.paddr_field() & !(level.size() - 1)) + offset),
            level,
        ))
    }

    #[inline(always)]
    pub fn phys_addr(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.translate(vaddr).map(|frame| frame.address())
    }

    /// Checks self-mappings using atomic observations. Arch whole-tree result
    /// requires the caller to exclude concurrent content updates.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        self.tree.validate()
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

    /// Removes exactly `page`.
    ///
    /// Inputs: a typed page and optional split invalidation scope. `None`
    /// forbids splitting; `Some(all_cpus)` permits it.
    ///
    /// Requires: `PS` must be a supported leaf level within this table, and the
    /// ownership policy must permit the page address.
    ///
    /// Returns: the removed entry, if mapped, and any remaining flush obligation.
    /// Returns [`PagingError::WrongPageSize`] when the existing mapping has a
    /// different leaf size and cannot or may not be split to `PS`.
    #[inline(always)]
    pub fn unmap<PS: PageSize>(
        &self,
        page: Page<PS>,
        split_all_cpus: Option<bool>,
    ) -> UnmapEntryResult<Arch> {
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        self.unmap_from(&self.root_view(), page, split_all_cpus)
    }

    /// Removes `page` below a previously validated pinned subtree.
    #[inline(always)]
    fn unmap_from<PS: PageSize, L: WalkLevelImpl>(
        &self,
        table: &PTPageRef<'_, Arch, Alloc, L>,
        page: Page<PS>,
        split_all_cpus: Option<bool>,
    ) -> UnmapEntryResult<Arch> {
        let vaddr = page.start_address();
        if L::LEVEL < PS::LEVEL {
            return Err(PagingError::WrongPageSize);
        }
        let index = entry_index(vaddr, L::LEVEL);
        let observed = table.load(index);
        if observed.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
            return self.unmap_from(&child, page, split_all_cpus);
        }

        let mut write = table.lock_to_update(&self.wperms);
        if L::LEVEL == PS::LEVEL {
            return match write.take_leaf(index) {
                Ok(None) => Ok((None, MayNeedFlush::none())),
                Ok(Some(entry)) => {
                    Ok((Some(entry), PTPage::<Arch, Alloc>::flush_for_leaf(vaddr, PS::LEVEL)))
                }
                Err(PagingError::NotLeafEntry) => {
                    let entry = write.load(index);
                    let child =
                        table.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
                    drop(write);
                    self.unmap_from(&child, page, split_all_cpus)
                }
                Err(error) => Err(error),
            };
        }

        let entry = write.load(index);
        if entry.is_present_table(L::LEVEL) {
            let child = table.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
            drop(write);
            return self.unmap_from(&child, page, split_all_cpus);
        }
        if !entry.present() {
            return Ok((None, MayNeedFlush::none()));
        }
        let all_cpus = split_all_cpus.ok_or(PagingError::WrongPageSize)?;
        // SAFETY: the content guard pins the entry and excludes competing writers.
        let flush = unsafe { write.split_leaf_to(index, page, all_cpus) }?;
        let child_entry = table.load(index);
        let child =
            table.child_from_observed(child_entry).map_err(|_| PagingError::NotLeafEntry)?;
        drop(write);
        let (entry, pending) = self.unmap_from(&child, page, None)?;
        Ok((entry, flush.and(pending)))
    }

    /// Splits the huge leaf represented by `page` one level while preserving
    /// its mappings. New pages are prepared privately; the content guard covers
    /// publication and flushing.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split(
        &self,
        page: Page<Huge>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        self.split_from(&self.root_view(), page, all_cpus)
    }

    /// Splits `page` below a validated pinned subtree.
    #[inline(always)]
    fn split_from<L: WalkLevelImpl>(
        &self,
        table: &PTPageRef<'_, Arch, Alloc, L>,
        page: Page<Huge>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let level = L::LEVEL;
        if level < Huge::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        let vaddr = page.start_address();
        let index = entry_index(vaddr, level);
        let observed = table.load(index);
        if observed.is_present_table(level) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::InvalidLevel)?;
            return self.split_from(&child, page, all_cpus);
        }
        if level != Huge::LEVEL {
            return Err(PagingError::InvalidLevel);
        }

        let mut write = table.lock_to_update(&self.wperms);
        // SAFETY: the content guard pins the entry and excludes software writers.
        match unsafe {
            write.split_leaf_to(index, Page::<Regular>::containing_address(vaddr), all_cpus)
        } {
            Err(PagingError::NotLeafEntry) => Err(PagingError::InvalidLevel),
            result => result,
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
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if PS::LEVEL > PageLevel::Level2 || PS::LEVEL > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        self.set_flags_from(&self.root_view(), page, Arch::filter_flags(flags), all_cpus)
    }

    /// Replaces flags below a validated pinned subtree.
    #[inline(always)]
    fn set_flags_from<PS: PageSize, L: WalkLevelImpl>(
        &self,
        table: &PTPageRef<'_, Arch, Alloc, L>,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if L::LEVEL < PS::LEVEL {
            return Err(PagingError::NotLeafEntry);
        }
        let vaddr = page.start_address();
        let index = entry_index(vaddr, L::LEVEL);
        let observed = table.load(index);
        if observed.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
            return self.set_flags_from(&child, page, flags, all_cpus);
        }

        let mut write = table.lock_to_update(&self.wperms);
        let current = write.load(index);
        if current.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry)?;
            drop(write);
            return self.set_flags_from(&child, page, flags, all_cpus);
        }
        // SAFETY: the content guard pins the entry and excludes software writers.
        unsafe { write.update_leaf_flags_at(index, page, flags, all_cpus) }
    }

    /// Retags `page` as shared, splitting if needed.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_shared<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.set_encryption(page, true, all_cpus)
    }

    /// Retags `page` as private.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_private<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.set_encryption(page, false, all_cpus)
    }

    /// Changes one policy-approved page's shared/private address tag.
    fn set_encryption<PS: PageSize>(
        &self,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > PageLevel::Level2 || target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        self.set_encryption_from(&self.root_view(), page, shared, all_cpus)
    }

    /// Changes encryption below a validated pinned subtree.
    #[inline(always)]
    fn set_encryption_from<PS: PageSize, L: WalkLevelImpl>(
        &self,
        table: &PTPageRef<'_, Arch, Alloc, L>,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if L::LEVEL < PS::LEVEL {
            return Err(PagingError::NotLeafEntry);
        }
        let index = entry_index(page.start_address(), L::LEVEL);
        let observed = table.load(index);
        if observed.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
            return self.set_encryption_from(&child, page, shared, all_cpus);
        }

        let mut write = table.lock_to_update(&self.wperms);
        let current = write.load(index);
        if current.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry)?;
            drop(write);
            return self.set_encryption_from(&child, page, shared, all_cpus);
        }
        // SAFETY: the content guard pins the entry and excludes software writers.
        unsafe { write.set_encryption_at(index, page, shared, all_cpus) }
    }

    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let view = self.root_view();
        let entry = view.load(idx);
        entry.is_present_table(view.level()).then(|| PhysAddr::from(entry.address()))
    }

    /// Detaches empty tables on one path into bounded batch storage.
    fn detach_page_tables_by_addr<'id>(
        &mut self,
        vaddr: VirtAddr,
        batch: &mut DetachBatch<'id, Arch::TlbFlushTok>,
        detached: &mut [Option<DetachedPageTable<'id, Arch, Alloc>>],
    ) -> usize {
        let (start, end) = batch.range();
        assert!(start <= vaddr && vaddr < end);
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, MaxLevel::LEVEL)) {
            return 0;
        }
        assert!(detached.iter().all(Option::is_none));
        let mut count = 0;
        self.tree.root_mut().detach_path(vaddr, &mut |tree| {
            detached[count] = Some(tree);
            count += 1;
        });
        if count != 0 {
            batch.record_detachment();
        }
        count
    }

    /// Detaches, flushes, and frees empty tables on one path, never the root.
    pub fn free_page_table_by_addr(
        &mut self,
        vaddr: VirtAddr,
        pending: MayNeedFlush<Arch::TlbFlushTok>,
    ) -> usize {
        assert!(vaddr.bits() <= usize::MAX - Regular::SIZE);
        with_detach_batch(vaddr, vaddr + Regular::SIZE, |mut batch| {
            batch.include(pending);
            let mut detached: [Option<_>; DETACHED_PATH_CAPACITY] = core::array::from_fn(|_| None);
            let count = self.detach_page_tables_by_addr(vaddr, &mut batch, &mut detached);
            let flushed = batch.flush_tlb_global_sync();
            for tree in detached.into_iter().flatten() {
                drop(tree.into_staged_after_flush(&flushed));
            }
            count
        })
    }

    /// Frees owned subtrees, retaining borrowed root entries and all data frames.
    /// # Safety
    /// Every owned child table must come from this allocator, with no other parent
    /// links. Exclude all other walkers and invalidate cached table pointers
    /// before reusing pages or resuming hardware walks.
    pub unsafe fn free_children(&mut self) {
        // SAFETY: the caller supplies ownership and quiescence for every selected subtree.
        unsafe { self.tree.root_mut().free_children(<Owned::Owned as OwnedIndices>::contains) };
    }

    /// Installs an owned subtree in an absent root entry.
    /// Installation consumes the child-level staged tree and transfers its
    /// ownership to this table.
    /// # Panics
    /// Panics if `idx` is not a root-page entry index or is not owned by this
    /// table's policy.
    pub fn populate_owned(
        &mut self,
        idx: usize,
        subtree: OwnedSubtree<Arch, Alloc, <MaxLevel as InnerLevel>::Child>,
    ) -> Result<(), PopulateError<OwnedSubtree<Arch, Alloc, <MaxLevel as InnerLevel>::Child>>>
    where
        MaxLevel: InnerLevel,
        <MaxLevel as InnerLevel>::Child: WalkLevel,
    {
        assert!(idx < PT_ENTRY_COUNT);
        assert!(self.tree.policy().owns_top_entry(idx));
        let subpage_pa = subtree.root_paddr();
        let desired = PTEntry::new_table(
            Arch::make_private_address(subpage_pa),
            Arch::PTFlags::parent_flags(),
        );
        let root = self.root_view();
        let mut write = root.lock_to_update(&self.wperms);
        if let Err(error) = write.publish_table(idx, desired) {
            return Err(PopulateError { error, subtree });
        }
        subtree.release();
        Ok(())
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Policy<Owned>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: OwnedIndices,
{
    /// Borrows the child table at `idx` from the same root position in `other`.
    /// Policies that leave the same index borrowed cannot populate one another:
    /// ```compile_fail,E0080
    /// use paging::address::{Address, PhysAddr, VirtAddr};
    /// use paging::level::Lvl;
    /// use paging::os_contract::{PagingAllocator, PagingError};
    /// use paging::pagetable::{LockSpec, PageTable};
    /// use paging::policy::{CoveredRange, Policy};
    /// use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};
    /// use std::sync::{Mutex, MutexGuard};
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// struct Platform;
    ///
    /// unsafe impl X86PagingParams for Platform {
    ///     fn private_mask() -> usize { 0 }
    ///     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    ///     fn flush_tlb_global_sync(_: FlushScope) {}
    /// }
    ///
    /// struct Allocator;
    ///
    /// unsafe impl PagingAllocator for Allocator {
    ///     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
    ///         VirtAddr::from(paddr.bits())
    ///     }
    ///     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
    ///         PhysAddr::from(vaddr.bits())
    ///     }
    ///     fn allocate_table_page() -> Result<PhysAddr, PagingError> {
    ///         unreachable!()
    ///     }
    ///     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// }
    ///
    /// struct Locks(Mutex<()>);
    ///
    /// unsafe impl LockSpec<()> for Locks {
    ///     type Guard<'a> = MutexGuard<'a, ()>;
    ///     fn lock(&self, _: PhysAddr) -> Self::Guard<'_> {
    ///         self.0.lock().unwrap()
    ///     }
    /// }
    ///
    /// type Table = PageTable<
    ///     X86Paging<Platform>, Allocator, Lvl<3>, Locks, (),
    ///     Policy<CoveredRange<0, 256>>,
    /// >;
    ///
    /// fn overlap(source: &Table, target: &mut Table) {
    ///     let _ = unsafe { target.populate_shared(256, source) };
    /// }
    ///
    /// fn main() {
    ///     let source = std::mem::MaybeUninit::<Table>::uninit();
    ///     let mut target = std::mem::MaybeUninit::<Table>::uninit();
    ///     unsafe {
    ///         overlap(source.assume_init_ref(), target.assume_init_mut());
    ///     }
    /// }
    /// ```
    /// # Panics
    /// Panics if `idx` is not a root-page entry index, is owned by this table,
    /// or is not owned by `other`.
    /// # Safety
    /// The caller must prevent the source from reclaiming its subtree at `idx`
    /// while this table can use it. The subtree must stay allocated at this
    /// same virtual prefix, and all software access must use the same
    /// atomic-access and content-lock protocol. Before reclaiming the subtree,
    /// unlink every sharing parent, then complete synchronous TLB and
    /// paging-structure-walk invalidation for all hardware users.
    pub unsafe fn populate_shared<SourceOwned>(
        &mut self,
        idx: usize,
        other: &PageTable<Arch, Alloc, MaxLevel, WP, T, Policy<SourceOwned>>,
    ) -> Result<(), PagingError>
    where
        SourceOwned: OwnedIndices,
    {
        assert_borrowed_disjoint_from::<_, Owned>(other.tree.policy());
        let entry = shared_top_entry::<_, _, _, _, _, Owned, _>(idx, other)?;
        let root = self.root_view();
        let result = root.lock_to_update(&self.wperms).publish_table(idx, entry);
        result
    }
}

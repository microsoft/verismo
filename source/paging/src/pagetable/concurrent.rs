//! The `pagetable` API with concurrent walks and serialized entry updates.
//! Shared borrows pin table pages; exclusive borrows permit reclamation.
//! External synchronization provides those borrows but does not fence hardware
//! walkers; the embedder supplies synchronous TLB hooks and hardware quiescence.
//!
//! # Public API
//!
//! - Types: [`PageTable`], [`KernelPageTable`], [`UserPageTable`],
//!   [`super::PagingMutex`],
//!   [`UnmapEntryResult`], and [`PopulateError`].
//! - Construction and ownership: [`PageTable::new`], [`PageTable::new_empty`], [`PageTable::from_root`],
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
//!   [`PageTable::populate_shared`], [`PageTable::release_shared`],
//!   [`PageTable::free_page_table_by_addr`],
//!   [`PageTable::cleanup_page_tables_by_range`], and
//!   [`PageTable::free_children`].
//! - Validation: [`PageTable::validate_page_table`].
use core::ops::Deref;
use core::sync::atomic::Ordering;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::level::{InnerLevel, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::policy::{
    compile_check_borrowed_disjoint_from, compile_check_matching_free_policy, KernelPolicy,
    MayShareSubtree, OwnedIndices, PagingOwnershipPolicy, UserPolicy,
};
use crate::structs::ptpage::{
    DetachedPageTable, Live, OwnedSubtree, PTPageRef, PTPageTree, WalkLevel,
};
use crate::structs::sizes::{entry_index, PageSize, Regular, PT_ENTRY_COUNT};
use crate::structs::tlb::{with_detach_batch, DetachBatch, MayNeedFlush};
use crate::structs::AllRootEntries;

const DETACHED_PATH_CAPACITY: usize = 4;

/// A failed owned-subtree installation that returns the unconsumed subtree.
pub struct PopulateError<S> {
    /// Why the subtree was not installed.
    pub error: PagingError,
    /// The still-unlinked subtree returned to the caller.
    pub subtree: S,
}

fn shared_top_entry<Arch, Alloc, MaxLevel, TargetOwned, SourceOwned>(
    idx: usize,
    other: &PageTable<Arch, Alloc, MaxLevel, SourceOwned>,
) -> Result<PTEntry<Arch>, PagingError>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    TargetOwned: OwnedIndices,
    SourceOwned: PagingOwnershipPolicy,
{
    assert!(idx < PT_ENTRY_COUNT);
    assert!(!TargetOwned::contains(idx, idx + 1));
    assert!(other.tree.policy().owns_top_entry(idx));
    let entry = other.root_view().load(idx);
    if !entry.present() {
        return Err(PagingError::NotMapped);
    }
    if !entry.is_present_table(MaxLevel::LEVEL) {
        return Err(PagingError::InvalidLevel);
    }
    Ok(entry)
}

/// Shared access permits walk, map, unmap and split, but never removes an
/// installed table pointer. Freeing needs `&mut self` and hardware exclusion.
/// Drop frees the root and owned descendant tables, never shared subtrees or data
/// frames. Owned CPU-local hardware bindings use [`crate::pagetable::ActivePageTable`];
/// externally managed hardware-active trees need `ManuallyDrop` or `leak`.
///
/// Mutation methods suffixed `_unchecked` skip only ownership-policy checks.
/// They are unsafe: callers must establish ownership of every affected root
/// entry. Structural validation, content locks, and flush obligations remain.
/// These entry points are intended for future verified callers; no Verus proof
/// currently establishes their preconditions.
///
/// ```compile_fail,E0133
/// use paging::{
///     pagetable::PageTable,
///     structs::{ArchPagingMeta, Page, PagingAllocator, WalkLevel},
/// };
///
/// fn remove<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevel>(
///     table: &PageTable<A, P, L>,
///     page: Page,
/// ) {
///     let _ = table.unmap_unchecked(page, None);
/// }
/// ```
pub struct PageTable<
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy = KernelPolicy<AllRootEntries>,
> {
    pub(super) tree: PTPageTree<Arch, Alloc, MaxLevel, Owned, Live>,
}

/// Arch concurrent kernel page table with cfg-selected content locking.
pub type KernelPageTable<Arch, Alloc, MaxLevel, Owned = AllRootEntries> =
    PageTable<Arch, Alloc, MaxLevel, KernelPolicy<Owned>>;
/// Arch concurrent user page table that may borrow some root entries from
/// another table (see [`PageTable::new_from_sharing_top`] and
/// [`PageTable::populate_shared`]).
pub type UserPageTable<Arch, Alloc, MaxLevel, Owned> =
    PageTable<Arch, Alloc, MaxLevel, UserPolicy<Owned>>;

impl<Arch, Alloc, MaxLevel, Owned> PageTable<Arch, Alloc, MaxLevel, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy + Default,
{
    /// Allocates an empty root using the default value of its ownership policy.
    ///
    /// No mappings or borrowed links are installed. The allocator must already
    /// provide writable access to table pages, but this new tree need not map
    /// those pages itself. Establish the required mappings before loading its
    /// root into hardware; self-mapping validation may fail until then.
    pub fn new_empty() -> Result<Self, PagingError> {
        let tree = PTPageTree::new_root(Owned::default())?.into_live();
        Ok(Self { tree })
    }
}

impl<Arch, Alloc, MaxLevel> PageTable<Arch, Alloc, MaxLevel, KernelPolicy>
where
    Arch: ArchPagingMeta,
    Alloc: DirectMappedAllocator,
    MaxLevel: WalkLevel,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let tree = PTPageTree::new_direct_mapped(flags)?;
        tree.validate()?;
        let tree = tree.into_live();
        Ok(Self { tree })
    }
}

impl<Arch, Alloc, MaxLevel> PageTable<Arch, Alloc, MaxLevel, KernelPolicy>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
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
    pub unsafe fn from_root(root_pa: PhysAddr) -> Result<Self, PagingError> {
        // SAFETY: tree accessibility and ownership are required by this constructor.
        let tree =
            unsafe { PTPageTree::<Arch, Alloc, MaxLevel, KernelPolicy>::from_root(root_pa) }?
                .into_live();
        Ok(Self { tree })
    }

    /// Borrows the root entries not selected by `TargetOwned`'s [`OwnedIndices`]
    /// set; those entries become immutable through the returned controller.
    /// The built-in locks serialize writers by physical table-page key.
    ///
    /// `SourceOwned` must implement [`MayShareSubtree`] — i.e. its
    /// [`PagingOwnershipPolicy::MAY_SHARE_SUBTREE`] must be `true` — checked
    /// at compile time. If `SourceOwned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned()`
    /// is `true`, every borrowed root entry's share count (see
    /// [`crate::structs::os_contract::PagingAllocator::share_count`]) is
    /// incremented before this returns; that is what lets
    /// [`Self::free_page_table_by_addr`] and
    /// [`Self::cleanup_page_tables_by_range`] refuse to free a top-level
    /// table page while any derived table still shares it, instead of
    /// relying solely on the `# Safety` contract below. `TargetOwned`'s
    /// `MAY_FREE_PAGE_TABLE_PAGES.frees_shared()` must agree with
    /// `SourceOwned`'s `.frees_owned()` (checked at compile time too), so
    /// the returned table's own `Drop` can later make the same tracking
    /// decision from its own policy alone.
    ///
    /// Unlocked source, sharing the low half of a kernel root:
    /// ```
    /// # use paging::{
    /// #     address::{Address, PhysAddr, VirtAddr},
    /// #     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    /// #     pagetable::{KernelPageTable, PageTable},
    /// #     structs::{CoveredRange, Lvl, PagingAllocator, PagingError, UserPolicy},
    /// # };
    /// # #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// # struct Platform;
    /// # unsafe impl X86_64PagingParams for Platform {
    /// #     fn private_mask() -> usize { 0 }
    /// #     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    /// #     fn flush_tlb_global_sync(_: FlushScope) {}
    /// # }
    /// # struct Allocator;
    /// # unsafe impl PagingAllocator for Allocator {
    /// #     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    /// #     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    /// #     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    /// #     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// # }
    /// type Arch = X86_64Paging<Platform>;
    /// type Kernel = KernelPageTable<Arch, Allocator, Lvl<3>>;
    ///
    /// fn derive_user_table(kernel: &Kernel) -> Result<(), PagingError> {
    ///     let _user = unsafe {
    ///         // `read` is the identity: `kernel` is already a plain reference.
    ///         Kernel::new_from_sharing_top::<UserPolicy<CoveredRange<256, 512>>, _, _, _>( kernel, |k| k,
    ///         )
    ///     }?;
    ///     Ok(())
    /// }
    /// ```
    ///
    /// Lock-protected source: `read` acquires the lock, and the guard is
    /// dropped as soon as the shared entries are copied, well before the
    /// derived table (or `kernel_lock`) is done being used.
    /// ```
    /// # use paging::{
    /// #     address::{Address, PhysAddr, VirtAddr},
    /// #     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    /// #     pagetable::{KernelPageTable, PageTable},
    /// #     structs::{CoveredRange, Lvl, PagingAllocator, PagingError, UserPolicy},
    /// # };
    /// # use std::sync::RwLock;
    /// # #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// # struct Platform;
    /// # unsafe impl X86_64PagingParams for Platform {
    /// #     fn private_mask() -> usize { 0 }
    /// #     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    /// #     fn flush_tlb_global_sync(_: FlushScope) {}
    /// # }
    /// # struct Allocator;
    /// # unsafe impl PagingAllocator for Allocator {
    /// #     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    /// #     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    /// #     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    /// #     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// # }
    /// type Arch = X86_64Paging<Platform>;
    /// type Kernel = KernelPageTable<Arch, Allocator, Lvl<3>>;
    ///
    /// fn derive_user_table(kernel_lock: &RwLock<Kernel>) -> Result<(), PagingError> {
    ///     let _user = unsafe {
    ///         Kernel::new_from_sharing_top::<UserPolicy<CoveredRange<256, 512>>, _, _, _>(
    ///             kernel_lock,
    ///             |lock| lock.read().unwrap(),
    ///         )
    ///     }?;
    ///     Ok(())
    /// }
    /// ```
    ///
    /// A policy that cannot be shared from is rejected at compile time:
    /// ```compile_fail
    /// use paging::{
    ///     address::{Address, PhysAddr, VirtAddr},
    ///     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    ///     pagetable::PageTable,
    ///     structs::{CoveredRange, Lvl, PagingAllocator, PagingError, UserPolicy},
    /// };
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// struct Platform;
    /// unsafe impl X86_64PagingParams for Platform {
    ///     fn private_mask() -> usize { 0 }
    ///     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    ///     fn flush_tlb_global_sync(_: FlushScope) {}
    /// }
    ///
    /// struct Allocator;
    /// unsafe impl PagingAllocator for Allocator {
    ///     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    ///     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    ///     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    ///     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// }
    ///
    ///
    /// type Arch = X86_64Paging<Platform>;
    /// // `MAY_SHARE_SUBTREE` is `false`, so this policy cannot be a source.
    /// type Source = PageTable<Arch, Allocator, Lvl<3>, UserPolicy<CoveredRange<0, 256>>>;
    ///
    /// // Never called: the bound `SourceOwned: MayShareSubtree` is checked
    /// // when this function is type-checked, whether or not it ever runs.
    /// fn derive(source: &Source) {
    ///     let _ = unsafe {
    ///         KernelPageTable::<Arch, Allocator, Lvl<3>>::
    ///             new_from_sharing_top::<UserPolicy<CoveredRange<256, 512>>, _, _, _>(source, |s| s)
    ///     };
    /// }
    /// ```
    /// # Safety
    ///
    /// The source page table should not free its PT pages at the MaxLevel - 1,
    /// to ensure that the shared top entries remain valid and will not point to reclaimed pages,
    /// which may poison the page table. [`Alloc::share_count`] backs this at
    /// runtime for [`Self::free_page_table_by_addr`] and
    /// [`Self::cleanup_page_tables_by_range`]: they refuse to free a
    /// top-level table page while its share count is nonzero (when
    /// `SourceOwned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned()` is `true`). A
    /// source that frees pages through some other, unrelated path is still
    /// out of scope for that check; and a source whose policy's
    /// `MAY_FREE_PAGE_TABLE_PAGES.frees_owned()` is `false` gets no runtime
    /// check at all, so it must genuinely never free a shared top-level page
    /// for as long as any derived table could still use it.
    ///
    /// `Drop` and [`Self::free_children`] also enforce this policy: tracked
    /// owned entries must have zero shares before reclamation, or they panic;
    /// entries whose policy forbids freeing are retained instead. These
    /// checks do not establish hardware quiescence or protect against raw
    /// deallocation outside this API. Every derived table must release its
    /// borrowed entries through `Drop` or [`Self::release_shared`] before a
    /// tracked source is reclaimed. Leaking a derived root transfers that
    /// release obligation to the caller.
    ///
    /// In a common case, this is called to derive a user page table from a
    /// kernel page table, sharing some top entries. Thus, we just need to
    /// ensure the kernel page table does not free its top-level PT pages before
    /// detaching them from all page tables — typically satisfied by keeping
    /// the kernel page table `'static` and leaked/never dropped.
    ///
    /// [`Alloc::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
    pub unsafe fn new_from_sharing_top<'src, TargetOwned, SourceOwned, Container, Guard>(
        source: &'src Container,
        read: impl FnOnce(&'src Container) -> Guard,
    ) -> Result<PageTable<Arch, Alloc, MaxLevel, TargetOwned>, PagingError>
    where
        TargetOwned: PagingOwnershipPolicy + Default,
        SourceOwned: PagingOwnershipPolicy + MayShareSubtree,
        Guard: Deref<Target = PageTable<Arch, Alloc, MaxLevel, SourceOwned>>,
    {
        const { compile_check_matching_free_policy::<TargetOwned, SourceOwned>() };
        // Use the target's root ownership even if copying or validation fails.
        let mut tree = PTPageTree::new_root(TargetOwned::default())?.into_live();
        {
            let source_ptb = read(source);
            compile_check_borrowed_disjoint_from::<_, TargetOwned::Owned>(source_ptb.tree.policy());
            for idx in (0..PT_ENTRY_COUNT)
                .filter(|index| !TargetOwned::Owned::contains(*index, *index + 1))
            {
                match shared_top_entry::<_, _, _, TargetOwned::Owned, _>(idx, &source_ptb) {
                    Ok(entry) => {
                        if SourceOwned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned() {
                            Alloc::share_count(PhysAddr::from(entry.address()))
                                .fetch_add(1, Ordering::AcqRel);
                        }
                        tree.root_mut().store(idx, entry);
                    }
                    Err(PagingError::NotMapped) => {}
                    Err(error) => return Err(error),
                }
            }
            drop(source_ptb);
        }
        tree.validate()?;
        Ok(PageTable { tree })
    }
}

impl<Arch, Alloc, MaxLevel, Owned> PageTable<Arch, Alloc, MaxLevel, UserPolicy<Owned>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: OwnedIndices,
{
    /// Transfers the raw root and policy without releasing shares.
    /// The caller must release borrowed links and their share counts before
    /// reclaiming the source or the leaked root.
    pub fn leak_with_policy(self) -> (UserPolicy<Owned>, PhysAddr) {
        self.leak_parts()
    }
}

impl<Arch, Alloc, MaxLevel, Owned> PageTable<Arch, Alloc, MaxLevel, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy,
{
    pub(super) const SMALL: PageLevel = PageLevel::Level0;

    /// Inputs: owned controller.
    /// Requires: none.
    /// Returns: policy and unreclaimed root.
    fn leak_parts(self) -> (Owned, PhysAddr) {
        self.tree.into_parts()
    }

    /// Gives up the tree and returns its root.
    /// Arch borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> PhysAddr {
        let (_, root_pa) = self.leak_parts();
        root_pa
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
        let top_idx = entry_index(vaddr, MaxLevel::LEVEL);
        if !self.tree.policy().owns_top_entry(top_idx) {
            return 0;
        }
        // A derived table may still hold a copy of this root entry (see
        // `PageTable::new_from_sharing_top`/`populate_shared`), but only if
        // this policy allows being shared from at all.
        if Owned::MAY_SHARE_SUBTREE {
            if Owned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned() {
                // Share-count tracking is active for this policy: refuse to
                // detach while `Alloc::share_count` says a share is still
                // outstanding.
                if let Some(paddr) = self.next_table_pa(top_idx) {
                    if Alloc::share_count(paddr).load(Ordering::Acquire) != 0 {
                        return 0;
                    }
                }
            } else {
                // No share-count tracking ever ran for this policy's owned
                // top-level entries, so there is no count to consult; per
                // `MayFreePageTablePages`'s contract this entry must never be
                // freed while it might still be shared, so refuse to detach
                // it here at all (leak it), matching `Drop`'s handling of
                // the same setting.
                return 0;
            }
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
    /// Refuses (returns `0` for the top-level entry) a still-shared root
    /// entry per [`Alloc::share_count`], and, when this policy's
    /// `MAY_FREE_PAGE_TABLE_PAGES.frees_owned()` is `false`, refuses
    /// unconditionally instead (no share count was ever tracked for it, so
    /// it must be leaked rather than risked); see
    /// [`Self::new_from_sharing_top`]/[`Self::populate_shared`].
    ///
    /// [`Alloc::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
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
    /// Enforces the same share-count contract as `Drop`: refuses (panics) to
    /// free a still-shared owned entry, and retains (leaks) owned entries
    /// instead of freeing them when this policy's
    /// `MAY_FREE_PAGE_TABLE_PAGES.frees_owned()` is `false`.
    /// # Safety
    /// Every owned child table actually freed (see the enforcement above,
    /// which additionally rules out any other software table still
    /// referencing it) must come from this allocator. Exclude all other
    /// (hardware) walkers and invalidate cached table pointers before
    /// reusing pages or resuming hardware walks.
    pub unsafe fn free_children(&mut self) {
        // SAFETY: the caller supplies ownership and quiescence for every selected subtree;
        // the share-count check inside `free_owned_children` additionally rules out any
        // other software table still referencing an owned entry before it is freed.
        unsafe { self.tree.free_owned_children() };
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
        let mut write = root.lock_to_update();
        if let Err(error) = write.publish_table(idx, desired) {
            return Err(PopulateError { error, subtree });
        }
        subtree.release();
        Ok(())
    }

    /// Borrows the child table at `idx` from the same root position in
    /// `other`.
    ///
    /// `SourceOwned` must implement [`MayShareSubtree`], checked at compile
    /// time. Like [`Self::new_from_sharing_top`], this table's own
    /// `MAY_FREE_PAGE_TABLE_PAGES.frees_shared()` must match `SourceOwned`'s
    /// `.frees_owned()` (also checked at compile time), and if that value is
    /// `true`, the borrowed entry's share count (see [`Alloc::share_count`])
    /// is incremented before this returns.
    ///
    /// Unlocked source:
    /// ```
    /// # use paging::{
    /// #     address::{Address, PhysAddr, VirtAddr},
    /// #     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    /// #     pagetable::{KernelPageTable, PageTable},
    /// #     structs::{CoveredRange, Lvl, PagingAllocator, PagingError},
    /// # };
    /// # #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// # struct Platform;
    /// # unsafe impl X86_64PagingParams for Platform {
    /// #     fn private_mask() -> usize { 0 }
    /// #     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    /// #     fn flush_tlb_global_sync(_: FlushScope) {}
    /// # }
    /// # struct Allocator;
    /// # unsafe impl PagingAllocator for Allocator {
    /// #     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    /// #     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    /// #     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    /// #     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// # }
    /// type Arch = X86_64Paging<Platform>;
    /// type Kernel = KernelPageTable<Arch, Allocator, Lvl<3>>;
    ///
    /// fn share_into<'owner>(
    ///     source: &'owner Kernel,
    ///     target: &mut paging::pagetable::UserPageTable<Arch, Allocator, Lvl<3>, CoveredRange<1, 512>>,
    /// ) -> Result<(), PagingError> {
    ///     unsafe { target.populate_shared(0, source, |s| s) }
    /// }
    /// ```
    ///
    /// Lock-protected source, mirroring [`Self::new_from_sharing_top`]:
    /// ```
    /// # use paging::{
    /// #     address::{Address, PhysAddr, VirtAddr},
    /// #     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    /// #     pagetable::{KernelPageTable, PageTable},
    /// #     structs::{CoveredRange, Lvl, PagingAllocator, PagingError},
    /// # };
    /// # use std::sync::RwLock;
    /// # #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// # struct Platform;
    /// # unsafe impl X86_64PagingParams for Platform {
    /// #     fn private_mask() -> usize { 0 }
    /// #     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    /// #     fn flush_tlb_global_sync(_: FlushScope) {}
    /// # }
    /// # struct Allocator;
    /// # unsafe impl PagingAllocator for Allocator {
    /// #     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    /// #     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    /// #     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    /// #     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// # }
    /// type Arch = X86_64Paging<Platform>;
    /// type Kernel = KernelPageTable<Arch, Allocator, Lvl<3>>;
    ///
    /// fn share_into<'owner>(
    ///     source_lock: &'owner RwLock<Kernel>,
    ///     target: &mut paging::pagetable::UserPageTable<Arch, Allocator, Lvl<3>, CoveredRange<1, 512>>,
    /// ) -> Result<(), PagingError> {
    ///     unsafe { target.populate_shared(0, source_lock, |lock| lock.read().unwrap()) }
    /// }
    /// ```
    ///
    /// A policy that cannot be shared from is rejected at compile time:
    /// ```compile_fail
    /// use paging::{
    ///     address::{Address, PhysAddr, VirtAddr},
    ///     arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    ///     pagetable::PageTable,
    ///     structs::{CoveredRange, Lvl, PagingAllocator, PagingError, UserPolicy},
    /// };
    ///
    /// #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    /// struct Platform;
    /// unsafe impl X86_64PagingParams for Platform {
    ///     fn private_mask() -> usize { 0 }
    ///     fn supported_flags() -> PTEntryFlags { PTEntryFlags::all() }
    ///     fn flush_tlb_global_sync(_: FlushScope) {}
    /// }
    ///
    /// struct Allocator;
    /// unsafe impl PagingAllocator for Allocator {
    ///     fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr { VirtAddr::from(paddr.bits()) }
    ///     fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr { PhysAddr::from(vaddr.bits()) }
    ///     fn allocate_table_page() -> Result<PhysAddr, PagingError> { unreachable!() }
    ///     unsafe fn deallocate_table_page(_: PhysAddr) {}
    /// }
    ///
    ///
    /// // `MAY_SHARE_SUBTREE` is `false`, so this policy cannot be a source.
    /// type Table = PageTable<X86_64Paging<Platform>, Allocator, Lvl<3>, UserPolicy<CoveredRange<0, 256>>>;
    ///
    /// // Never called: the bound `SourceOwned: MayShareSubtree` is checked
    /// // when this function is type-checked, whether or not it ever runs.
    /// fn overlap(source: &Table, target: &mut Table) {
    ///     let _ = unsafe { target.populate_shared(256, source, |s| s) };
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
    /// [`Alloc::share_count`] backs this at runtime the same way it does for
    /// [`Self::new_from_sharing_top`].
    ///
    /// [`Alloc::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
    pub unsafe fn populate_shared<'src, SourceOwned, Container, Guard>(
        &mut self,
        idx: usize,
        other: &'src Container,
        read: impl FnOnce(&'src Container) -> Guard,
    ) -> Result<(), PagingError>
    where
        SourceOwned: PagingOwnershipPolicy + MayShareSubtree,
        Guard: Deref<Target = PageTable<Arch, Alloc, MaxLevel, SourceOwned>>,
    {
        const { compile_check_matching_free_policy::<Owned, SourceOwned>() };
        let other_ptb = read(other);
        compile_check_borrowed_disjoint_from::<_, Owned::Owned>(other_ptb.tree.policy());
        let entry = shared_top_entry::<_, _, _, Owned::Owned, _>(idx, &other_ptb)?;
        if SourceOwned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned() {
            Alloc::share_count(PhysAddr::from(entry.address())).fetch_add(1, Ordering::AcqRel);
        }
        drop(other_ptb);
        let root = self.root_view();
        let result = root.lock_to_update().publish_table(idx, entry);
        if result.is_err() && SourceOwned::MAY_FREE_PAGE_TABLE_PAGES.frees_owned() {
            Alloc::share_count(PhysAddr::from(entry.address())).fetch_sub(1, Ordering::Release);
        }
        result
    }

    /// Releases this table's share of a borrowed (non-owned) root entry
    /// installed by [`Self::new_from_sharing_top`]/[`Self::populate_shared`],
    /// resetting the slot back to absent and decrementing
    /// [`Alloc::share_count`] first (when
    /// `Owned::MAY_FREE_PAGE_TABLE_PAGES.frees_shared()`).
    ///
    /// Dropping this whole table already releases every remaining borrowed
    /// entry the same way, so this is only needed to give up one entry
    /// earlier than the table's own lifetime, e.g. to reuse the slot via
    /// [`Self::populate_owned`]/[`Self::populate_shared`] before then.
    ///
    /// # Panics
    /// Panics if `idx` is not a root-page entry index or is owned (not
    /// borrowed) by this table.
    /// # Safety
    /// No walker or software accessor may still observe this subtree through
    /// this table: exclude every walker and invalidate cached table pointers,
    /// exactly as required before reclaiming an owned subtree.
    ///
    /// [`Alloc::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
    pub unsafe fn release_shared(&mut self, idx: usize) -> Result<PhysAddr, PagingError> {
        // SAFETY: the caller guarantees no walker or software accessor still
        // observes this subtree through this table.
        unsafe { self.tree.release_shared_entry(idx) }
    }
}

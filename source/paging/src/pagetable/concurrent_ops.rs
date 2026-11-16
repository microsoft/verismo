//! Page-level read/mutation operations on [`PageTable`]: walking, mapping,
//! unmapping, splitting, and flag/encryption changes. Construction, teardown,
//! and subtree-ownership transfer live in [`super::concurrent`] instead.

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::os_contract::{PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy};
use crate::structs::ptpage::{
    PTPage, PTPageRef, PTPageTree, Translation, WalkLevel, WalkLevelImpl, WalkResult,
};
use crate::structs::sizes::{entry_index, Huge, PageSize, Regular};
use crate::structs::tlb::MayNeedFlush;

use super::PageTable;

/// A removed entry paired with any TLB invalidation it leaves outstanding.
pub type UnmapEntryResult<A> =
    Result<(Option<PTEntry<A>>, MayNeedFlush<<A as ArchPagingMeta>::TlbFlushTok>), PagingError>;

impl<Arch, Alloc, MaxLevel, Owned> PageTable<Arch, Alloc, MaxLevel, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy,
{
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
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        // SAFETY: the policy check authorizes the target root entry.
        unsafe { self.map_with_parent_flags_unchecked(page, frame, flags, shared, parent_flags) }
    }

    /// [`Self::map_with_parent_flags`] without the ownership-policy check.
    /// Level validation, flag filtering, and content locking are unchanged.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller,
    /// not borrowed from another table.
    #[inline(always)]
    pub unsafe fn map_with_parent_flags_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        let paddr = frame.start_address();
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
            let mut write = table.lock_to_update();
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

        let mut write = table.lock_to_update();
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

    /// [`Self::map`] without the ownership-policy check.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    #[inline(always)]
    pub unsafe fn map_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        // SAFETY: the caller authorizes the target root entry.
        unsafe {
            self.map_with_parent_flags_unchecked(
                page,
                frame,
                flags,
                shared,
                Arch::PTFlags::parent_flags(),
            )
        }
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
        // SAFETY: the policy check authorizes the target root entry.
        unsafe { self.unmap_unchecked(page, split_all_cpus) }
    }

    /// [`Self::unmap`] without the ownership-policy check.
    /// Leaf-size checks, splitting, and flush obligations are unchanged.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    /// The split synchronization requirements of [`Self::unmap`] still apply.
    #[inline(always)]
    pub unsafe fn unmap_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        split_all_cpus: Option<bool>,
    ) -> UnmapEntryResult<Arch> {
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

        let mut write = table.lock_to_update();
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
        // SAFETY: the policy check authorizes the target root entry.
        unsafe { self.split_unchecked(page, all_cpus) }
    }

    /// [`Self::split`] without the ownership-policy check.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    /// The synchronization requirements of [`Self::split`] still apply.
    #[inline(always)]
    pub unsafe fn split_unchecked(
        &self,
        page: Page<Huge>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
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

        let mut write = table.lock_to_update();
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
        // SAFETY: the policy check authorizes the target root entry.
        unsafe { self.set_flags_unchecked(page, flags, all_cpus) }
    }

    /// [`Self::set_flags`] without the ownership-policy check.
    /// Flag/level validation and flush obligations are unchanged.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    /// The synchronization requirements of [`Self::set_flags`] still apply.
    #[inline(always)]
    pub unsafe fn set_flags_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
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

        let mut write = table.lock_to_update();
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

    /// [`Self::set_shared`] without the ownership-policy check.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    /// The synchronization requirements of [`Self::set_shared`] still apply.
    #[inline(always)]
    pub unsafe fn set_shared_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        // SAFETY: the caller authorizes the target root entry.
        unsafe { self.set_encryption_unchecked(page, true, all_cpus) }
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

    /// [`Self::set_private`] without the ownership-policy check.
    ///
    /// # Safety
    /// The root entry containing `page` must be owned by this controller.
    /// The synchronization requirements of [`Self::set_private`] still apply.
    #[inline(always)]
    pub unsafe fn set_private_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        // SAFETY: the caller authorizes the target root entry.
        unsafe { self.set_encryption_unchecked(page, false, all_cpus) }
    }

    /// Changes one policy-approved page's shared/private address tag.
    fn set_encryption<PS: PageSize>(
        &self,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        // SAFETY: the policy check authorizes the target root entry.
        unsafe { self.set_encryption_unchecked(page, shared, all_cpus) }
    }

    /// # Safety
    /// The caller must authorize the target root entry and satisfy the
    /// synchronization requirements of the checked encryption operations.
    #[inline(always)]
    unsafe fn set_encryption_unchecked<PS: PageSize>(
        &self,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = PS::LEVEL;
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

        let mut write = table.lock_to_update();
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
}

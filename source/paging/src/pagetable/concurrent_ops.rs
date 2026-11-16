//! Atomic walks, translation, and self-mapping validation on page-table controllers.
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PagingAllocator, PagingError};
use crate::structs::policy::PagingOwnershipPolicy;
use crate::structs::ptpage::{Translation, WalkLevel, WalkResult};
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
}

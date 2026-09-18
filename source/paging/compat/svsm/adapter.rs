//! Owned and borrowed page tables using SVSM's allocator and platform policy.

use crate::address::{Address, PhysAddr, VirtAddr};
use crate::cpu::TlbFlushScope;
use crate::mm::pagetable::{PTEntryFlags, PTPage, Pml4Level, SvsmPaging};
use crate::mm::{phys_to_virt, virt_to_phys, PageBox};
use crate::types::PageSize;
use crate::utils::MemoryRegion;
use core::fmt;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Range;
use core::ptr::NonNull;
use paging::traits::ArchPagingMeta as SvsmArch;
use verismo_paging::address::{Address as _, PhysAddr as VerismoPhys, VirtAddr as VerismoVirt};
use verismo_paging::mapping::MappingRefOps;
use verismo_paging::os_contract::DirectMappedAllocator;
use verismo_paging::sizes::{Size1GiB, Size2MiB, Size4KiB};
use verismo_paging::tlb::TlbFlush;
use verismo_paging::{ArchPagingMeta, PTEntryFlags as VerismoFlags};

pub use verismo_paging::level::PageLevel;
pub use verismo_paging::os_contract::PagingError;

pub type Flush = verismo_paging::tlb::MayNeedFlush<TlbFlushScope>;
pub type NativePageTable = paging::pagetable::InstalledPageTable<SvsmPaging, SvsmPaging, Pml4Level>;

#[derive(Clone, Copy, Debug)]
struct Architecture;

impl ArchPagingMeta for Architecture {
    type PTFlags = VerismoFlags;
    type TlbFlushTok = TlbFlushScope;

    fn private_pte_mask() -> usize {
        <SvsmPaging as SvsmArch>::private_pte_mask()
    }

    fn shared_pte_mask() -> usize {
        <SvsmPaging as SvsmArch>::shared_pte_mask()
    }

    fn address_mask() -> usize {
        <SvsmPaging as SvsmArch>::address_mask()
    }

    fn supported_flags() -> VerismoFlags {
        VerismoFlags::from_bits_truncate(<SvsmPaging as SvsmArch>::supported_flags().bits())
    }

    fn split_leaf_attributes(entry: usize, level: PageLevel) -> usize {
        ((entry >> 12) & 1) << if level == PageLevel::Level1 { 7 } else { 12 }
    }

    fn accessed_dirty_mask() -> usize {
        (VerismoFlags::ACCESSED | VerismoFlags::DIRTY).bits()
    }

    fn leaf_flags_mask() -> Self::PTFlags {
        VerismoFlags::WRITABLE | VerismoFlags::USER | VerismoFlags::GLOBAL | VerismoFlags::NX
    }

    fn requires_break_before_make(_old: usize, _new: usize, _level: PageLevel) -> bool {
        false
    }
}

impl TlbFlush for TlbFlushScope {
    fn range(start: VerismoVirt, end: VerismoVirt, level: PageLevel) -> Self {
        let size = match level {
            PageLevel::Level0 => PageSize::Regular,
            PageLevel::Level1 => PageSize::Huge,
            _ => return Self::all(),
        };
        Self::range(MemoryRegion::new(VirtAddr::from(start.bits()), end - start), size)
    }

    fn all() -> Self {
        Self::all()
    }

    fn and(self, other: Self) -> Self {
        <Self as paging::tlb::TlbFlush>::and(self, other)
    }

    fn flush_tlb_global_sync(self) {
        flush_scope(self.with_global(true), true);
    }

    fn flush_tlb_ignore_global_sync(self) {
        flush_scope(self.with_global(false), true);
    }

    fn flush_tlb_global_percpu(self) {
        flush_scope(self.with_global(true), false);
    }

    fn flush_tlb_ignore_global_percpu(self) {
        flush_scope(self.with_global(false), false);
    }
}

fn flush_scope(scope: TlbFlushScope, all_cpus: bool) {
    #[cfg(all(test, not(test_in_svsm)))]
    tests::record_transition_flush(scope, all_cpus);
    #[cfg(not(all(test, not(test_in_svsm))))]
    if all_cpus {
        scope.flush_all_cpus();
    } else {
        scope.flush_percpu();
    }
}

struct Allocator;

impl Allocator {
    fn root_memory() -> Result<(Range<VerismoPhys>, VerismoVirt), PagingError> {
        let (pa, va, size) = crate::mm::alloc::root_memory_mapping();
        if size == 0 {
            return Err(PagingError::InvalidRange);
        }
        Ok((
            VerismoPhys::from(pa.bits())..VerismoPhys::from(pa.bits() + size),
            VerismoVirt::from(va.bits()),
        ))
    }

    fn virtual_range() -> Result<Range<usize>, PagingError> {
        let (physical, virtual_base) = Self::root_memory()?;
        Ok(virtual_base.bits()..virtual_base.bits() + (physical.end - physical.start))
    }
}

// SAFETY: SVSM's root arena has a fixed private mapping. PageBox allocates
// unique aligned pages in it; these pages are explicitly zeroed before return.
unsafe impl DirectMappedAllocator for Allocator {
    fn direct_map() -> (Range<VerismoPhys>, VerismoVirt) {
        Self::root_memory().expect("SVSM root memory must remain initialized")
    }

    fn allocate_table_page() -> Result<VerismoPhys, PagingError> {
        let page = PageBox::<PTPage>::try_new_zeroed().map_err(|_| PagingError::AllocFrame)?;
        let pa = VerismoPhys::from(virt_to_phys(page.vaddr()).bits());
        assert!(Self::direct_map().0.contains(&pa));
        assert_eq!(phys_to_virt(PhysAddr::from(pa.bits())), page.vaddr());
        let _ = PageBox::leak(page);
        Ok(pa)
    }

    fn allocate_zeroed_table_page() -> Result<VerismoPhys, PagingError> {
        Self::allocate_table_page()
    }

    unsafe fn deallocate_table_page(pa: VerismoPhys) {
        let va = phys_to_virt(PhysAddr::from(pa.bits()));
        let ptr = NonNull::new(va.as_mut_ptr::<PTPage>()).unwrap();
        // SAFETY: the tree returns only detached frames allocated above.
        drop(unsafe { PageBox::from_raw(ptr) });
    }
}

type Inner = verismo_paging::pagetable::KernelPageTable<
    Architecture,
    Allocator,
    verismo_paging::level::Lvl<3>,
>;

const _: () = {
    assert!(core::mem::size_of::<PTPage>() == 4096);
    assert!(core::mem::align_of::<PTPage>() == 4096);
    assert!(core::mem::size_of::<crate::mm::pagetable::PTEntry>() == core::mem::size_of::<usize>());
};

#[derive(Clone, Copy, Debug)]
pub struct Mapping {
    pub frame: PhysAddr,
    /// Leaf flags; restrictions in ancestor entries still apply.
    pub flags: PTEntryFlags,
    pub level: PageLevel,
    pub shared: bool,
}

impl PartialEq for Mapping {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame
            && self.flags.bits() == other.flags.bits()
            && self.level == other.level
            && self.shared == other.shared
    }
}

impl Eq for Mapping {}

/// An owned unpublished tree or an exclusive borrow of an acyclic SVSM tree.
/// Page-size transitions publish first and synchronously flush all CPUs.
pub struct PageTable<'a> {
    inner: ManuallyDrop<Inner>,
    arena: Range<usize>,
    owns_children: bool,
    native: PhantomData<&'a mut NativePageTable>,
}

impl fmt::Debug for PageTable<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PageTable").field("root", &self.root_paddr()).finish()
    }
}

impl PageTable<'static> {
    /// # Safety
    /// SVSM paging and root memory must be initialized. The root arena must
    /// remain mapped privately and must not be reset until this table is dropped.
    /// Before dropping it, quiesce hardware users and release all external
    /// aliases to its exclusively owned root and descendant table pages.
    pub unsafe fn new() -> Result<Self, PagingError> {
        let arena = Allocator::virtual_range()?;
        let inner = ManuallyDrop::new(Inner::new(VerismoFlags::data())?);
        Ok(Self { inner, arena, owns_children: true, native: PhantomData })
    }
}

impl<'a> PageTable<'a> {
    /// Borrows existing SVSM pages; all pages remain owned by their native owner.
    ///
    /// # Safety
    /// All table pages must stay privately mapped in SVSM's root arena.
    /// Except for the standard recursive root entry, which is rejected, the
    /// tree must be acyclic, with no different-prefix table aliases. Exclude
    /// access through all other software controllers during this borrow.
    /// If paging's default `use_ad` feature is disabled, import sets A/D on all
    /// present entries after validation. Quiesce hardware, software walkers and
    /// all table aliases during import, then invalidate paging-structure caches
    /// and TLBs before resuming any user.
    /// Permit synchronous SVSM shootdowns: do not block IPI delivery or hold
    /// exclusion that an interrupt handler can reenter. Keep the transition's
    /// code, stack and shootdown state accessible throughout the callback.
    pub unsafe fn from_svsm(native: &'a mut NativePageTable) -> Result<Self, PagingError> {
        if native.next_table_pa(crate::mm::PGTABLE_LVL3_IDX_PTE_SELFMAP).is_some() {
            return Err(PagingError::InvalidAddress);
        }
        let arena = Allocator::virtual_range()?;
        // SAFETY: the caller supplies an acyclic, accessible tree and excludes
        // other controllers. ManuallyDrop leaves all table pages with the native owner.
        let inner = ManuallyDrop::new(unsafe {
            Inner::from_root(VerismoPhys::from(native.root_pa().bits()))
        }?);
        Ok(Self { inner, arena, owns_children: false, native: PhantomData })
    }

    pub fn root_paddr(&self) -> PhysAddr {
        PhysAddr::from(self.inner.root_paddr().bits())
    }

    pub fn mapping(&self, va: VirtAddr) -> Result<Mapping, PagingError> {
        let mapping = self.inner.walk(VerismoVirt::from(va.bits()));
        let entry = mapping.read();
        if !entry.is_leaf(mapping.level()) {
            return Err(PagingError::NotMapped);
        }
        Ok(snapshot(entry, mapping.level()))
    }

    pub fn phys_addr(&self, va: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.inner.phys_addr(VerismoVirt::from(va.bits())).map(|pa| PhysAddr::from(pa.bits()))
    }

    pub fn map(
        &mut self,
        va: VirtAddr,
        pa: PhysAddr,
        level: PageLevel,
        flags: PTEntryFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.check_page(va, level)?;
        check_physical(pa, level)?;
        let flags = convert_flags(flags)?;
        match level {
            PageLevel::Level0 => self.inner.map(
                verismo_paging::page::Page::<Size4KiB>::from_start_address(va.bits().into())
                    .unwrap(),
                verismo_paging::frame::PhysFrame::<Size4KiB>::from_start_address(pa.bits().into())
                    .unwrap(),
                flags,
                shared,
            ),
            PageLevel::Level1 => self.inner.map(
                verismo_paging::page::Page::<Size2MiB>::from_start_address(va.bits().into())
                    .unwrap(),
                verismo_paging::frame::PhysFrame::<Size2MiB>::from_start_address(pa.bits().into())
                    .unwrap(),
                flags,
                shared,
            ),
            PageLevel::Level2 => self.inner.map(
                verismo_paging::page::Page::<Size1GiB>::from_start_address(va.bits().into())
                    .unwrap(),
                verismo_paging::frame::PhysFrame::<Size1GiB>::from_start_address(pa.bits().into())
                    .unwrap(),
                flags,
                shared,
            ),
            _ => Err(PagingError::InvalidLevel),
        }
    }

    pub fn split(&mut self, va: VirtAddr, level: PageLevel) -> Result<Flush, PagingError> {
        self.check_page(va, level)?;
        match level {
            PageLevel::Level0 => self.inner.split(
                verismo_paging::page::Page::<Size4KiB>::containing_address(va.bits().into()),
                true,
            ),
            PageLevel::Level1 => self.inner.split(
                verismo_paging::page::Page::<Size2MiB>::containing_address(va.bits().into()),
                true,
            ),
            PageLevel::Level2 => self.inner.split(
                verismo_paging::page::Page::<Size1GiB>::containing_address(va.bits().into()),
                true,
            ),
            _ => Err(PagingError::InvalidLevel),
        }
    }

    pub fn mprotect(
        &mut self,
        va: VirtAddr,
        level: PageLevel,
        flags: PTEntryFlags,
    ) -> Result<Flush, PagingError> {
        self.check_page(va, level)?;
        let flags = convert_flags(flags)?;
        match level {
            PageLevel::Level0 => self.inner.set_flags(
                verismo_paging::page::Page::<Size4KiB>::from_start_address(va.bits().into())
                    .unwrap(),
                flags,
                true,
            ),
            PageLevel::Level1 => self.inner.set_flags(
                verismo_paging::page::Page::<Size2MiB>::from_start_address(va.bits().into())
                    .unwrap(),
                flags,
                true,
            ),
            PageLevel::Level2 => self.inner.set_flags(
                verismo_paging::page::Page::<Size1GiB>::from_start_address(va.bits().into())
                    .unwrap(),
                flags,
                true,
            ),
            _ => Err(PagingError::InvalidLevel),
        }
    }

    pub fn mprotect_range(
        &mut self,
        region: MemoryRegion<VirtAddr>,
        flags: PTEntryFlags,
    ) -> (Result<(), PagingError>, Flush) {
        let validated = self
            .check_range(region.start().bits(), region.len())
            .and_then(|()| convert_flags(flags));
        match validated {
            Ok(flags) => self.inner.set_flags_range(
                region.start().bits().into(),
                region.end().bits().into(),
                flags,
                true,
            ),
            Err(error) => (Err(error), Flush::none()),
        }
    }

    pub fn unmap(
        &mut self,
        va: VirtAddr,
        level: PageLevel,
    ) -> Result<(Option<Mapping>, Flush), PagingError> {
        self.check_page(va, level)?;
        let old = match level {
            PageLevel::Level0 => self.inner.unmap(
                verismo_paging::page::Page::<Size4KiB>::from_start_address(va.bits().into())
                    .unwrap(),
                true,
            ),
            PageLevel::Level1 => self.inner.unmap(
                verismo_paging::page::Page::<Size2MiB>::from_start_address(va.bits().into())
                    .unwrap(),
                true,
            ),
            PageLevel::Level2 => self.inner.unmap(
                verismo_paging::page::Page::<Size1GiB>::from_start_address(va.bits().into())
                    .unwrap(),
                true,
            ),
            _ => Err(PagingError::InvalidLevel),
        };
        let (old, flush) = old?;
        Ok((old.map(|entry| snapshot(entry, level)), flush))
    }

    fn check_page(&self, va: VirtAddr, level: PageLevel) -> Result<(), PagingError> {
        if level > PageLevel::Level2 {
            return Err(PagingError::InvalidLevel);
        }
        if !va.is_aligned(level.size()) {
            return Err(PagingError::InvalidAddress);
        }
        self.check_range(va.bits(), level.size())
    }

    fn check_range(&self, start: usize, size: usize) -> Result<(), PagingError> {
        let end = start.checked_add(size).ok_or(PagingError::InvalidRange)?;
        if (start | size) & 4095 != 0 {
            return Err(PagingError::InvalidRange);
        }
        if size != 0 && start < self.arena.end && self.arena.start < end {
            return Err(PagingError::InvalidAddress);
        }
        if VerismoVirt::from(start).bits() != start
            || (size != 0
                && (VerismoVirt::from(end - 1).bits() != end - 1
                    || (start >> 47) != ((end - 1) >> 47)))
        {
            return Err(PagingError::InvalidAddress);
        }
        Ok(())
    }
}

impl Drop for PageTable<'_> {
    fn drop(&mut self) {
        // SAFETY: this is the only extraction, and the field will not be accessed again.
        let inner = unsafe { ManuallyDrop::take(&mut self.inner) };
        if self.owns_children {
            drop(inner);
        } else {
            let _ = inner.leak();
        }
    }
}

fn convert_flags(flags: PTEntryFlags) -> Result<VerismoFlags, PagingError> {
    let flags = VerismoFlags::from_bits(flags.bits()).ok_or(PagingError::InvalidFlags)?;
    if !flags.contains(VerismoFlags::PRESENT) {
        return Err(PagingError::InvalidFlags);
    }
    Ok(flags)
}

fn check_physical(pa: PhysAddr, level: PageLevel) -> Result<(), PagingError> {
    let mask = Architecture::address_mask()
        & !(Architecture::private_pte_mask() | Architecture::shared_pte_mask());
    if !pa.is_aligned(level.size()) || pa.bits() & !mask != 0 {
        return Err(PagingError::InvalidAddress);
    }
    Ok(())
}

fn snapshot(entry: verismo_paging::entry::PTEntry<Architecture>, level: PageLevel) -> Mapping {
    Mapping {
        frame: PhysAddr::from(entry.leaf_address(level).bits()),
        flags: PTEntryFlags::from_bits_truncate(entry.flags().bits()),
        level,
        shared: Architecture::is_shared_address(VerismoPhys::from(entry.paddr_field())),
    }
}

#[cfg(all(test, not(test_in_svsm)))]
#[path = "verismo_paging_tests.rs"]
mod tests;

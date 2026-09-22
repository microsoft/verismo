// SPDX-License-Identifier: MIT

use core::{fmt, marker::PhantomData, mem::ManuallyDrop};
use litebox::mm::linux::{PageFaultError, PageRange, VmFlags, VmemPageFaultHandler};
use litebox::platform::{page_mgmt, RawConstPointer as _};
use paging::{
    address::{Address, PhysAddr as PagingPhysAddr, VirtAddr as PagingVirtAddr},
    frame::PhysFrame as PagingPhysFrame,
    level::{Lvl, PageLevel},
    os_contract::{PagingAllocator, PagingError},
    page::Page as PagingPage,
    pagetable::{KernelPageTable as ConcurrentPageTable, LockSpec},
    sizes::{Huge as PagingHuge, Regular as PagingRegular},
    tlb::MayNeedFlush,
    FlushScope, PTEntryFlags, X86Paging, X86PagingParams, X86TlbFlushTok,
};
use spin::mutex::{SpinMutex, SpinMutexGuard};
use x86_64::{
    structures::{
        idt::PageFaultErrorCode,
        paging::{Page, PageTable, PageTableFlags, Regular},
    },
    PhysAddr, VirtAddr,
};

use crate::{
    mm::{
        pgtable::{
            assert_user_range, validate_user_parents, PageTableAllocator, PageTableImpl,
            USER_ADDRESS_END, USER_PARENT_FLAGS,
        },
        MemoryProvider,
    },
    UserMutPtr,
};

struct Platform<M>(PhantomData<fn() -> M>);

impl<M> Copy for Platform<M> {}
impl<M> Clone for Platform<M> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<M> PartialEq for Platform<M> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<M> Eq for Platform<M> {}
impl<M> fmt::Debug for Platform<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("LiteBoxPaging")
    }
}

#[cfg(test)]
static FLUSHES: SpinMutex<alloc::vec::Vec<FlushScope>> = SpinMutex::new(alloc::vec::Vec::new());

// The host must pin this address space to one CPU for its entire active lifetime.
const FLUSH_ALL_CPUS: bool = false;

unsafe impl<M: MemoryProvider + 'static> X86PagingParams for Platform<M> {
    fn private_mask() -> usize {
        M::PRIVATE_PTE_MASK as usize
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_: FlushScope) {
        panic!("LiteBox has no cross-CPU TLB shootdown interface");
    }

    fn flush_tlb_global_percpu(scope: FlushScope) {
        let scope = match scope {
            FlushScope::Range { start, end, .. } if end - start > 2 * 1024 * 1024 => {
                FlushScope::All
            }
            scope => scope,
        };
        #[cfg(test)]
        {
            tests::observe_transition_flush();
            FLUSHES.lock().push(scope);
        }
        #[cfg(not(test))]
        match scope {
            FlushScope::Range { start, end, .. } => {
                for address in (start.bits()..end.bits()).step_by(4096) {
                    x86_64::instructions::tlb::flush(VirtAddr::new(address as u64));
                }
            }
            FlushScope::All => x86_64::instructions::interrupts::without_interrupts(|| unsafe {
                use x86_64::registers::control::{Cr4, Cr4Flags};
                let flags = Cr4::read_raw();
                // A PGE transition invalidates global and PCID-tagged translations.
                Cr4::write_raw(flags ^ Cr4Flags::PAGE_GLOBAL.bits());
                Cr4::write_raw(flags);
            }),
        }
    }
}

// MemoryProvider supplies unique private frames and their stable writable host mapping.
unsafe impl<M: MemoryProvider + 'static> PagingAllocator for Platform<M> {
    fn paddr_to_vaddr(address: PagingPhysAddr) -> PagingVirtAddr {
        PagingVirtAddr::from(M::pa_to_va(PhysAddr::new(address.bits() as u64)).as_u64() as usize)
    }

    fn vaddr_to_paddr(address: PagingVirtAddr) -> PagingPhysAddr {
        PagingPhysAddr::from(
            (M::va_to_pa(VirtAddr::new(address.bits() as u64)).as_u64() & !M::PRIVATE_PTE_MASK)
                as usize,
        )
    }

    fn allocate_table_page() -> Result<PagingPhysAddr, PagingError> {
        // Fault handling also uses this path for anonymous data pages.
        let frame = PageTableAllocator::<M>::allocate_frame(true).ok_or(PagingError::AllocFrame)?;
        Ok(((frame.start_address().as_u64() & !M::PRIVATE_PTE_MASK) as usize).into())
    }

    unsafe fn deallocate_table_page(address: PagingPhysAddr) {
        unsafe { M::mem_free_pages(Self::paddr_to_vaddr(address).as_mut_ptr(), 0) };
    }
}

static CONTENT_LOCK: SpinMutex<()> = SpinMutex::new(());
struct ContentLock;

// All boot-root adapters share this exclusion domain, including inherited tables.
unsafe impl LockSpec<()> for ContentLock {
    type Guard<'a> = SpinMutexGuard<'a, ()>;

    fn lock(&self, _: PagingPhysAddr) -> Self::Guard<'_> {
        CONTENT_LOCK.lock()
    }
}

type Tree<M> = ConcurrentPageTable<X86Paging<Platform<M>>, Platform<M>, Lvl<3>, ContentLock>;
type Flush<M> = MayNeedFlush<X86TlbFlushTok<Platform<M>>>;

pub struct X64PageTable<'a, M: MemoryProvider + 'static, const ALIGN: usize> {
    inner: SpinMutex<ManuallyDrop<Tree<M>>>,
    borrowed_root: PhantomData<&'a mut PageTable>,
}

impl<M: MemoryProvider + 'static, const ALIGN: usize> Drop for X64PageTable<'_, M, ALIGN> {
    fn drop(&mut self) {
        // SAFETY: exclusive destruction takes the controller exactly once.
        let tree = unsafe { ManuallyDrop::take(self.inner.get_mut()) };
        let _ = tree.leak();
    }
}

pub(crate) fn vmflags_to_pteflags(values: VmFlags) -> PageTableFlags {
    let mut flags = PageTableFlags::empty();
    flags.set(
        PageTableFlags::USER_ACCESSIBLE,
        values.intersects(VmFlags::VM_READ | VmFlags::VM_WRITE),
    );
    flags.set(PageTableFlags::WRITABLE, values.contains(VmFlags::VM_WRITE));
    flags.set(PageTableFlags::NO_EXECUTE, !values.contains(VmFlags::VM_EXEC));
    flags
}

fn parent_flags() -> PTEntryFlags {
    paging_flags(USER_PARENT_FLAGS)
}

fn paging_flags(flags: PageTableFlags) -> PTEntryFlags {
    PTEntryFlags::from_bits_retain(flags.bits() as usize)
}

fn host_flags(entry: paging::entry::PTEntry<impl paging::ArchPagingMeta>) -> PageTableFlags {
    PageTableFlags::from_bits_truncate(entry.raw() as u64)
}

fn flush_local<M: MemoryProvider + 'static>(flush: Flush<M>) {
    if flush.is_pending() {
        flush.flush_tlb_global_percpu();
    }
}

impl<M: MemoryProvider + 'static, const ALIGN: usize> X64PageTable<'_, M, ALIGN> {
    fn split_to_4k(inner: &Tree<M>, address: PagingVirtAddr) -> Result<(), PagingError> {
        loop {
            let mapping = inner.walk(address);
            if !mapping.read().present() {
                return Err(PagingError::NotMapped);
            }
            let flush = match mapping.level() {
                PageLevel::Level0 => return Ok(()),
                PageLevel::Level1 => inner.split(
                    PagingPage::<PagingHuge>::containing_address(address),
                    FLUSH_ALL_CPUS,
                ),
                PageLevel::Level2 => inner.set_flags(
                    PagingPage::<PagingRegular>::containing_address(address),
                    mapping.read().flags(),
                    FLUSH_ALL_CPUS,
                ),
                _ => return Err(PagingError::InvalidLevel),
            }?;
            flush_local::<M>(flush);
        }
    }

    /// # Safety
    /// Boot-root imports preserve existing entry bits. Keep the tree stable
    /// during validation and coordinate all hardware and software users.
    pub(crate) unsafe fn new(root: PhysAddr) -> Self {
        unsafe { Self::init(root) }
    }

    pub(crate) fn map_pages(
        &self,
        range: PageRange<ALIGN>,
        flags: VmFlags,
        populate_pages: bool,
    ) -> UserMutPtr<u8> {
        assert_user_range(range);
        if populate_pages {
            for address in range {
                let page = Page::from_start_address(VirtAddr::new(address as u64)).unwrap();
                unsafe {
                    PageTableImpl::handle_page_fault(
                        self,
                        page,
                        vmflags_to_pteflags(flags),
                        PageFaultErrorCode::empty(),
                    )
                }
                .expect("Failed to handle page fault");
            }
        }
        UserMutPtr::from_usize(range.start)
    }

    pub(crate) unsafe fn unmap_pages(
        &self,
        range: PageRange<ALIGN>,
        dealloc_frames: bool,
    ) -> Result<(), page_mgmt::DeallocationError> {
        assert_user_range(range);
        if !range.start.is_multiple_of(4096) || !range.end.is_multiple_of(4096) {
            return Err(page_mgmt::DeallocationError::Unaligned);
        }
        let inner = self.inner.lock();
        for address in (range.start..range.end).step_by(4096) {
            let address = PagingVirtAddr::from(address);
            let (entry, flush) = inner
                .unmap(
                    PagingPage::<PagingRegular>::from_start_address(address).unwrap(),
                    Some(FLUSH_ALL_CPUS),
                )
                .expect("kernel page-table policy permits unmapping");
            flush_local::<M>(flush);
            if let Some(entry) = entry {
                if dealloc_frames {
                    unsafe {
                        M::mem_free_pages(
                            M::pa_to_va(PhysAddr::new(
                                entry.leaf_address(PageLevel::Level0).bits() as u64,
                            ))
                            .as_mut_ptr(),
                            0,
                        )
                    };
                }
            }
        }
        Ok(())
    }

    pub(crate) unsafe fn remap_pages(
        &self,
        old_range: PageRange<ALIGN>,
        new_range: PageRange<ALIGN>,
    ) -> Result<UserMutPtr<u8>, page_mgmt::RemapError> {
        assert_user_range(old_range);
        assert_user_range(new_range);
        if [old_range.start, old_range.end, new_range.start, new_range.end]
            .into_iter()
            .any(|address| !address.is_multiple_of(4096))
        {
            return Err(page_mgmt::RemapError::Unaligned);
        }
        if old_range.start.max(new_range.start) < old_range.end.min(new_range.end) {
            return Err(page_mgmt::RemapError::Overlapping);
        }
        assert!(new_range.end - new_range.start >= old_range.end - old_range.start);
        let inner = self.inner.lock();
        for address in (new_range.start..new_range.end).step_by(4096) {
            if inner.walk(address.into()).read().present() {
                return Err(page_mgmt::RemapError::AlreadyAllocated);
            }
        }
        for old in (old_range.start..old_range.end).step_by(4096) {
            let old_address = PagingVirtAddr::from(old);
            match Self::split_to_4k(&inner, old_address) {
                Ok(()) => {}
                Err(PagingError::NotMapped) => continue,
                Err(PagingError::AllocFrame) => return Err(page_mgmt::RemapError::OutOfMemory),
                Err(error) => panic!("invalid source mapping: {error:?}"),
            }
            let entry = inner.walk(old_address).read();
            let new = new_range.start + old - old_range.start;
            let flags = paging_flags(host_flags(entry));
            inner
                .map_with_parent_flags(
                    PagingPage::<PagingRegular>::from_start_address(new.into()).unwrap(),
                    PagingPhysFrame::<PagingRegular>::from_start_address(
                        entry.leaf_address(PageLevel::Level0),
                    )
                    .unwrap(),
                    flags,
                    entry.paddr_field() & M::PRIVATE_PTE_MASK as usize == 0,
                    parent_flags(),
                )
                .map_err(|error| match error {
                    PagingError::AllocFrame => page_mgmt::RemapError::OutOfMemory,
                    PagingError::EntryAlreadyPresent { .. } | PagingError::NotLeafEntry => {
                        page_mgmt::RemapError::AlreadyAllocated
                    }
                    error => panic!("invalid destination mapping: {error:?}"),
                })?;
            flush_local::<M>(Flush::<M>::new(new.into(), PageLevel::Level0));
            let (removed, flush) = inner
                .unmap(
                    PagingPage::<PagingRegular>::from_start_address(old_address).unwrap(),
                    Some(FLUSH_ALL_CPUS),
                )
                .expect("kernel page-table policy permits unmapping");
            assert!(removed.is_some());
            flush_local::<M>(flush);
        }
        Ok(UserMutPtr::from_usize(new_range.start))
    }

    pub(crate) unsafe fn mprotect_pages(
        &self,
        range: PageRange<ALIGN>,
        new_flags: VmFlags,
    ) -> Result<(), page_mgmt::PermissionUpdateError> {
        assert_user_range(range);
        if !range.start.is_multiple_of(4096) || !range.end.is_multiple_of(4096) {
            return Err(page_mgmt::PermissionUpdateError::Unaligned);
        }
        let desired = vmflags_to_pteflags(new_flags) & Self::MPROTECT_PTE_MASK;
        let inner = self.inner.lock();
        for address in (range.start..range.end).step_by(4096) {
            let address = PagingVirtAddr::from(address);
            let mapping = inner.walk(address);
            if !mapping.read().is_present_leaf(mapping.level()) {
                continue;
            }
            let old_flags = host_flags(mapping.read());
            // LiteBox's COW path, not mprotect, grants a previously read-only page write access.
            let desired = if !old_flags.contains(PageTableFlags::WRITABLE) {
                desired - PageTableFlags::WRITABLE
            } else {
                desired
            };
            let flags = paging_flags((old_flags & !Self::MPROTECT_PTE_MASK) | desired);
            let flush = inner
                .set_flags(
                    PagingPage::<PagingRegular>::from_start_address(address).unwrap(),
                    flags,
                    FLUSH_ALL_CPUS,
                )
                .unwrap_or_else(|error| panic!("cannot update page permissions: {error:?}"));
            flush_local::<M>(flush);
        }
        Ok(())
    }
}

impl<M: MemoryProvider + 'static, const ALIGN: usize> PageTableImpl<ALIGN>
    for X64PageTable<'_, M, ALIGN>
{
    unsafe fn init(root: PhysAddr) -> Self {
        assert_eq!(ALIGN, 4096);
        assert!(root.is_aligned(4096u64));
        unsafe { validate_user_parents::<M>(root) }
            .expect("boot user ancestors must be writable, user-accessible and executable");
        let tree = ManuallyDrop::new(
            unsafe {
                Tree::<M>::from_root(
                    ContentLock,
                    ((root.as_u64() & !M::PRIVATE_PTE_MASK) as usize).into(),
                )
            }
            .expect("boot root must map every reachable table page"),
        );
        Self { inner: SpinMutex::new(tree), borrowed_root: PhantomData }
    }

    #[cfg(test)]
    fn translate(&self, address: VirtAddr) -> crate::arch::TranslateResult {
        use crate::arch::{MappedFrame, TranslateResult};
        use x86_64::structures::paging::{PhysFrame, SizeLevel2, Huge};
        let inner = self.inner.lock();
        let mapping = inner.walk((address.as_u64() as usize).into());
        let entry = mapping.read();
        if !entry.is_present_leaf(mapping.level()) {
            return TranslateResult::NotMapped;
        }
        let physical = PhysAddr::new((entry.paddr_field() & !(mapping.level().size() - 1)) as u64);
        let frame = match mapping.level() {
            PageLevel::Level0 => {
                MappedFrame::Regular(PhysFrame::<Regular>::from_start_address(physical).unwrap())
            }
            PageLevel::Level1 => {
                MappedFrame::Huge(PhysFrame::<Huge>::from_start_address(physical).unwrap())
            }
            PageLevel::Level2 => {
                MappedFrame::SizeLevel2(PhysFrame::<SizeLevel2>::from_start_address(physical).unwrap())
            }
            level => panic!("invalid x86 leaf level: {level:?}"),
        };
        TranslateResult::Mapped {
            frame,
            offset: address.as_u64() & (mapping.level().size() as u64 - 1),
            flags: host_flags(entry),
        }
    }

    unsafe fn handle_page_fault(
        &self,
        page: Page<Regular>,
        flags: PageTableFlags,
        error_code: PageFaultErrorCode,
    ) -> Result<(), PageFaultError> {
        if page.start_address().as_u64() >= USER_ADDRESS_END as u64 {
            return Err(PageFaultError::AccessError("kernel address is not a user mapping"));
        }
        let address = PagingVirtAddr::from(page.start_address().as_u64() as usize);
        let inner = self.inner.lock();
        let existing = inner.walk(address);
        if existing.read().present() {
            if error_code.contains(PageFaultErrorCode::CAUSED_BY_WRITE) {
                return if existing.read().writable() {
                    Ok(())
                } else {
                    Err(PageFaultError::AccessError("LiteBox COW is not implemented"))
                };
            }
            return if error_code.contains(PageFaultErrorCode::PROTECTION_VIOLATION) {
                Err(PageFaultError::AccessError("protection fault on present page"))
            } else {
                Ok(())
            };
        }
        let frame =
            Platform::<M>::allocate_table_page().map_err(|_| PageFaultError::AllocationFailed)?;
        match inner.map_with_parent_flags(
            PagingPage::<PagingRegular>::from_start_address(address).unwrap(),
            PagingPhysFrame::<PagingRegular>::from_start_address(frame).unwrap(),
            paging_flags(flags | PageTableFlags::PRESENT),
            false,
            parent_flags(),
        ) {
            Ok(()) => {
                flush_local::<M>(Flush::<M>::new(address, PageLevel::Level0));
                Ok(())
            }
            Err(error) => {
                unsafe { Platform::<M>::deallocate_table_page(frame) };
                match error {
                    PagingError::AllocFrame => Err(PageFaultError::AllocationFailed),
                    PagingError::EntryAlreadyPresent { .. } | PagingError::NotLeafEntry => {
                        Err(PageFaultError::HugePage)
                    }
                    error => panic!("invalid fault mapping: {error:?}"),
                }
            }
        }
    }
}

impl<M: MemoryProvider + 'static, const ALIGN: usize> VmemPageFaultHandler
    for X64PageTable<'_, M, ALIGN>
{
    unsafe fn handle_page_fault(
        &self,
        fault_addr: usize,
        flags: VmFlags,
        error_code: u64,
    ) -> Result<(), PageFaultError> {
        unsafe {
            PageTableImpl::handle_page_fault(
                self,
                Page::containing_address(VirtAddr::new(fault_addr as u64)),
                vmflags_to_pteflags(flags),
                PageFaultErrorCode::from_bits_truncate(error_code),
            )
        }
    }

    fn access_error(error_code: u64, flags: VmFlags) -> bool {
        let error_code = PageFaultErrorCode::from_bits_truncate(error_code);
        if error_code.contains(PageFaultErrorCode::CAUSED_BY_WRITE) {
            return !flags.contains(VmFlags::VM_WRITE);
        }
        error_code.contains(PageFaultErrorCode::PROTECTION_VIOLATION)
            || (flags & VmFlags::VM_ACCESS_FLAGS).is_empty()
    }
}

#[cfg(test)]
#[path = "verismo_tests.rs"]
mod tests;

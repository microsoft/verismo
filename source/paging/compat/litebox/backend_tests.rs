use super::*;
extern crate std;

use crate::{arch::TranslateResult, host::mock::MockKernel, mm::tests::test_root};
use core::cell::Cell;
use core::sync::atomic::{AtomicUsize, Ordering};
use litebox::platform::page_mgmt::MemoryRegionPermissions;

type MockTable = X64PageTable<'static, MockKernel, 4096>;

unsafe fn load_entry<A: paging::ArchPagingMeta>(
    entry: *const paging::entry::PTEntry<A>,
) -> paging::entry::PTEntry<A> {
    let word = unsafe { AtomicUsize::from_ptr(entry.cast_mut().cast::<usize>()) };
    let bits = word.load(Ordering::Acquire);
    unsafe { (&bits as *const usize).cast().read() }
}

std::thread_local! {
    static TRANSITION_PTE: Cell<*mut usize> = const { Cell::new(core::ptr::null_mut()) };
    static TRANSITION_FLUSHES: Cell<usize> = const { Cell::new(0) };
}

pub(super) fn observe_transition_flush() {
    let pte = TRANSITION_PTE.with(Cell::get);
    if !pte.is_null() {
        let word = unsafe { AtomicUsize::from_ptr(pte) }.load(Ordering::Acquire);
        assert_ne!(word & PTEntryFlags::PRESENT.bits(), 0);
        assert_eq!(word & PTEntryFlags::HUGE.bits(), 0);
        assert!(CONTENT_LOCK.is_locked());
        TRANSITION_FLUSHES.with(|count| count.set(count.get() + 1));
    }
}

struct ObservedTransition<'a>(PhantomData<&'a Tree<MockKernel>>);

impl Drop for ObservedTransition<'_> {
    fn drop(&mut self) {
        TRANSITION_PTE.with(|pte| pte.set(core::ptr::null_mut()));
    }
}

fn observe_transition(inner: &Tree<MockKernel>, address: PagingVirtAddr) -> ObservedTransition<'_> {
    let mut page = inner.root_paddr();
    for level in (0..4).rev() {
        let pte = unsafe {
            Platform::<MockKernel>::paddr_to_vaddr(page)
                .as_mut_ptr::<paging::entry::PTEntry<X86Paging<Platform<MockKernel>>>>()
                .add((address.bits() >> (12 + 9 * level)) & 511)
        };
        let entry = unsafe { load_entry(pte) };
        assert!(entry.present());
        if level == 0 || entry.huge() {
            TRANSITION_PTE.with(|current| assert!(current.replace(pte.cast()).is_null()));
            TRANSITION_FLUSHES.with(|count| count.set(0));
            return ObservedTransition(PhantomData);
        }
        page = entry.address().into();
    }
    unreachable!()
}

fn table() -> MockTable {
    unsafe { MockTable::init(test_root().start_address()) }
}

fn permissions(table: &MockTable, address: usize) -> (u64, PageTableFlags) {
    match table.translate(VirtAddr::new(address as u64)) {
        TranslateResult::Mapped { frame, offset, flags } => {
            (frame.start_address().as_u64() + offset, flags)
        }
        other => panic!("expected mapping: {other:?}"),
    }
}

fn effective_permissions(table: &MockTable, address: usize) -> PageTableFlags {
    let inner = table.inner.lock();
    crate::mm::tests::effective_flags(PhysAddr::new(inner.root_paddr().bits() as u64), address)
}

fn ancestor_words(table: &MockTable, address: usize) -> alloc::vec::Vec<usize> {
    let inner = table.inner.lock();
    let mut page = inner.root_paddr();
    let mut words = alloc::vec::Vec::new();
    for level in (1..=3).rev() {
        let index = (address >> (12 + 9 * level)) & 511;
        let pte = unsafe {
            Platform::<MockKernel>::paddr_to_vaddr(page)
                .as_mut_ptr::<paging::entry::PTEntry<X86Paging<Platform<MockKernel>>>>()
                .add(index)
        };
        let entry = unsafe { load_entry(pte) };
        words.push(entry.raw());
        page = entry.address().into();
    }
    words
}

#[test]
fn platform_clone_does_not_require_provider_clone() {
    struct NonCloneProvider;
    let platform = Platform::<NonCloneProvider>(PhantomData);
    assert_eq!(platform, platform.clone());
}

#[test]
fn real_permissions_preserve_prot_none_and_cow_policy() {
    let table = table();
    let address = 0x4000;
    let range = PageRange::new(address, address + 4096).unwrap();
    let permissions = MemoryRegionPermissions::READ | MemoryRegionPermissions::WRITE;
    table.map_pages(range, VmFlags::from(permissions), true);
    let (frame, initial) = self::permissions(&table, address);
    assert!(initial.contains(
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::WRITABLE
    ));

    unsafe { table.mprotect_pages(range, VmFlags::from(MemoryRegionPermissions::empty())) }
        .unwrap();
    let (protected_frame, protected) = self::permissions(&table, address);
    assert_eq!(frame, protected_frame);
    assert!(protected.contains(PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE));
    assert!(!protected.intersects(PageTableFlags::USER_ACCESSIBLE | PageTableFlags::WRITABLE));
    assert!(MockTable::access_error(PageFaultErrorCode::USER_MODE.bits(), VmFlags::empty()));

    unsafe { table.mprotect_pages(range, VmFlags::VM_READ | VmFlags::VM_WRITE) }.unwrap();
    let (_, restored) = self::permissions(&table, address);
    assert!(restored.contains(PageTableFlags::USER_ACCESSIBLE));
    assert!(!restored.contains(PageTableFlags::WRITABLE));
    assert!(matches!(
        unsafe {
            PageTableImpl::handle_page_fault(
                &table,
                Page::from_start_address(VirtAddr::new(address as u64)).unwrap(),
                vmflags_to_pteflags(VmFlags::VM_READ | VmFlags::VM_WRITE),
                PageFaultErrorCode::CAUSED_BY_WRITE | PageFaultErrorCode::PROTECTION_VIOLATION,
            )
        },
        Err(PageFaultError::AccessError("LiteBox COW is not implemented"))
    ));
    unsafe { table.unmap_pages(range, true) }.unwrap();
}

#[test]
fn split_and_protect_preserve_neighbors_and_tlb_scope() {
    let table = table();
    let address = PagingVirtAddr::from(0x4000_0000usize);
    let physical = PagingPhysAddr::from(0x2000_0000usize);
    let flags = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER;
    let inner = table.inner.lock();
    inner
        .map(
            paging::page::Page::<paging::sizes::Huge>::from_start_address(address).unwrap(),
            paging::frame::PhysFrame::<paging::sizes::Huge>::from_start_address(physical)
                .unwrap(),
            flags,
            false,
        )
        .unwrap();
    let snapshot = inner.walk(address);
    let protected = address + 4096;
    let observation = observe_transition(&inner, protected);
    let flush_start = FLUSHES.lock().len();
    let flush = inner
        .set_flags(
            paging::page::Page::<paging::sizes::Regular>::from_start_address(protected).unwrap(),
            flags - PTEntryFlags::WRITABLE,
            FLUSH_ALL_CPUS,
        )
        .unwrap();
    flush.expect_no_flush();
    assert_eq!(TRANSITION_FLUSHES.with(Cell::get), 1);
    assert!(matches!(
        FLUSHES.lock()[flush_start..],
        [FlushScope::Range { start, end, level: PageLevel::Level1 }]
            if start == address && end == address + 2 * 1024 * 1024
    ));
    drop(observation);
    assert_eq!(snapshot.level(), PageLevel::Level1);
    assert_eq!(inner.walk(protected).level(), PageLevel::Level0);
    assert!(!inner.walk(protected).read().writable());
    assert!(inner.walk(address).read().writable());
    assert!(inner.walk(address + 8192).read().writable());
    assert_eq!(inner.phys_addr(address + 123).unwrap(), physical + 123);

    inner
        .split(
            PagingPage::<PagingHuge>::containing_address(address),
            FLUSH_ALL_CPUS,
        )
        .expect_err("the mapping is already finer than Huge");
    let flush = inner
        .set_flags(
            paging::page::Page::<paging::sizes::Regular>::from_start_address(protected).unwrap(),
            flags,
            FLUSH_ALL_CPUS,
        )
        .unwrap();
    assert!(flush.is_pending());
    flush_local::<MockKernel>(flush);
    assert!(inner.walk(protected).read().writable());
    assert_eq!(inner.phys_addr(protected).unwrap(), physical + 4096);
    assert_eq!(inner.phys_addr(address + 8192).unwrap(), physical + 8192);
    let (result, flush) = inner.set_flags_range(
        address,
        address + 3 * 4096,
        flags - PTEntryFlags::WRITABLE,
        FLUSH_ALL_CPUS,
    );
    result.unwrap();
    flush_local::<MockKernel>(flush);
    assert!(!inner.walk(address + 8192).read().writable());
    assert!(inner.walk(address + 3 * 4096).read().writable());
    inner.validate_page_table().unwrap();
    assert!(FLUSHES.lock().iter().any(|scope| matches!(
        scope,
        FlushScope::Range { start, level: PageLevel::Level1, .. } if *start == address
    )));
    let (_, pending) = inner.unmap_region(address, address + 2 * 1024 * 1024).unwrap();
    flush_local::<MockKernel>(pending);
}

#[test]
fn move_existing_mapping_retains_frame_and_collision_is_non_destructive() {
    let table = table();
    let old = PageRange::new(0x1000, 0x2000).unwrap();
    let destination = PageRange::new(0x4000, 0x5000).unwrap();
    table.map_pages(old, VmFlags::VM_READ, true);
    table.map_pages(destination, VmFlags::VM_READ | VmFlags::VM_WRITE, true);
    let source_before = permissions(&table, old.start);
    let destination_before = permissions(&table, destination.start);
    let source_data = MockKernel::pa_to_va(PhysAddr::new(source_before.0)).as_mut_ptr::<u8>();
    unsafe {
        assert!(core::slice::from_raw_parts(source_data, 4096).iter().all(|byte| *byte == 0));
        source_data.write_bytes(0x5a, 4096);
    }
    assert!(matches!(
        unsafe { table.remap_pages(old, destination) },
        Err(page_mgmt::RemapError::AlreadyAllocated)
    ));
    assert_eq!(permissions(&table, old.start), source_before);
    assert_eq!(permissions(&table, destination.start), destination_before);
    unsafe { table.unmap_pages(destination, true) }.unwrap();
    unsafe { table.remap_pages(old, destination) }.unwrap();
    assert_eq!(permissions(&table, destination.start), source_before);
    unsafe {
        assert!(core::slice::from_raw_parts(source_data, 4096).iter().all(|byte| *byte == 0x5a));
    }
    assert!(matches!(table.translate(VirtAddr::new(old.start as u64)), TranslateResult::NotMapped));
    unsafe { table.unmap_pages(destination, true) }.unwrap();
}

#[test]
fn borrowed_root_survives_adapter_drop_and_validates_real_table_mappings() {
    let root = test_root().start_address();
    {
        let table = unsafe { MockTable::init(root) };
        table.inner.lock().validate_page_table().unwrap();
    }
    let table = unsafe { MockTable::init(root) };
    table.map_pages(PageRange::new(0x6000, 0x7000).unwrap(), VmFlags::VM_READ, true);
    assert!(permissions(&table, 0x6000).1.contains(PageTableFlags::PRESENT));
    table.inner.lock().validate_page_table().unwrap();
    unsafe { table.unmap_pages(PageRange::new(0x6000, 0x7000).unwrap(), true) }.unwrap();
}

#[test]
fn partial_range_failure_retains_flush_obligation() {
    let table = table();
    let range = PageRange::new(0x9000, 0xa000).unwrap();
    table.map_pages(range, VmFlags::VM_READ | VmFlags::VM_WRITE, true);
    let inner = table.inner.lock();
    let (result, flush) = inner.set_flags_range(
        range.start.into(),
        (range.end + 4096).into(),
        PTEntryFlags::PRESENT | PTEntryFlags::USER,
        FLUSH_ALL_CPUS,
    );
    assert_eq!(result, Err(PagingError::NotMapped));
    assert!(flush.is_pending());
    flush_local::<MockKernel>(flush);
    assert!(!inner.walk(range.start.into()).read().writable());
    drop(inner);
    unsafe { table.unmap_pages(range, true) }.unwrap();
}

#[test]
fn host_spin_locks_serialize_parallel_permission_updates() {
    extern crate std;

    let table = table();
    std::thread::scope(|scope| {
        for index in 0..4 {
            let table = &table;
            scope.spawn(move || {
                let start = 0x20_0000 + index * 4096;
                let range = PageRange::new(start, start + 4096).unwrap();
                table.map_pages(range, VmFlags::VM_READ, true);
                for _ in 0..64 {
                    unsafe { table.mprotect_pages(range, VmFlags::empty()) }.unwrap();
                    assert!(!permissions(table, start).1.contains(PageTableFlags::USER_ACCESSIBLE));
                    unsafe { table.mprotect_pages(range, VmFlags::VM_READ) }.unwrap();
                    assert!(permissions(table, start).1.contains(PageTableFlags::USER_ACCESSIBLE));
                }
                unsafe { table.unmap_pages(range, true) }.unwrap();
            });
        }
    });
}

#[test]
fn allocator_failure_is_reported_as_a_real_litebox_fault_error() {
    struct NoFrames;
    impl MemoryProvider for NoFrames {
        const GVA_OFFSET: VirtAddr = MockKernel::GVA_OFFSET;
        const PRIVATE_PTE_MASK: u64 = 0;

        fn mem_allocate_pages(_: u32) -> Option<*mut u8> {
            None
        }

        unsafe fn mem_free_pages(pointer: *mut u8, order: u32) {
            unsafe { MockKernel::mem_free_pages(pointer, order) };
        }

        fn va_to_pa(address: VirtAddr) -> PhysAddr {
            MockKernel::va_to_pa(address)
        }

        fn pa_to_va(address: PhysAddr) -> VirtAddr {
            MockKernel::pa_to_va(address)
        }
    }

    let table = unsafe { X64PageTable::<NoFrames, 4096>::init(test_root().start_address()) };
    let result = unsafe {
        PageTableImpl::handle_page_fault(
            &table,
            Page::from_start_address(VirtAddr::new(0x40_0000)).unwrap(),
            vmflags_to_pteflags(VmFlags::VM_READ),
            PageFaultErrorCode::empty(),
        )
    };
    assert!(matches!(result, Err(PageFaultError::AllocationFailed)));
    assert!(matches!(table.translate(VirtAddr::new(0x40_0000)), TranslateResult::NotMapped));
}

#[test]
fn first_read_only_nx_leaf_does_not_restrict_writable_executable_sibling() {
    let table = table();
    let first = PageRange::new(0x50_0000, 0x50_1000).unwrap();
    let sibling = PageRange::new(0x50_1000, 0x50_2000).unwrap();
    let flush_start = FLUSHES.lock().len();
    table.map_pages(first, VmFlags::VM_READ, true);
    let ancestors = ancestor_words(&table, first.start);
    table.map_pages(sibling, VmFlags::VM_READ | VmFlags::VM_WRITE | VmFlags::VM_EXEC, true);
    assert_eq!(ancestor_words(&table, first.start), ancestors);
    assert_eq!(
        effective_permissions(&table, first.start),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::NO_EXECUTE
    );
    assert_eq!(
        effective_permissions(&table, sibling.start),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::WRITABLE
    );
    assert!(!FLUSHES.lock()[flush_start..].contains(&FlushScope::All));
    for range in [first, sibling] {
        unsafe { table.unmap_pages(range, true) }.unwrap();
    }
}

#[test]
fn relocating_read_only_leaf_creates_permissive_new_ancestors() {
    let table = table();
    let source = PageRange::new(0x60_0000, 0x60_1000).unwrap();
    let start = (1usize << 39) + 4096;
    let destination = PageRange::new(start, start + 4096).unwrap();
    let sibling = PageRange::new(start + 4096, start + 8192).unwrap();
    table.map_pages(source, VmFlags::VM_READ, true);
    let source_before = permissions(&table, source.start);
    unsafe { table.remap_pages(source, destination) }.unwrap();
    let ancestors = ancestor_words(&table, destination.start);
    table.map_pages(sibling, VmFlags::VM_READ | VmFlags::VM_WRITE | VmFlags::VM_EXEC, true);
    assert_eq!(ancestor_words(&table, destination.start), ancestors);
    assert_eq!(permissions(&table, destination.start), source_before);
    assert_eq!(
        effective_permissions(&table, destination.start),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::NO_EXECUTE
    );
    assert_eq!(
        effective_permissions(&table, sibling.start),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::WRITABLE
    );
    unsafe { table.mprotect_pages(destination, VmFlags::VM_READ | VmFlags::VM_EXEC) }.unwrap();
    assert_eq!(
        effective_permissions(&table, destination.start),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE
    );
    for range in [destination, sibling] {
        unsafe { table.unmap_pages(range, true) }.unwrap();
    }
}

#[test]
fn restrictive_imported_user_ancestors_are_rejected_without_normalization() {
    extern crate std;

    let table = table();
    let root = PhysAddr::new(table.inner.lock().root_paddr().bits() as u64);
    let range = PageRange::new(0x90_0000, 0x90_1000).unwrap();
    table.map_pages(range, VmFlags::VM_READ | VmFlags::VM_WRITE | VmFlags::VM_EXEC, true);
    drop(table);
    let mut page = root;
    for level in (1..=3).rev() {
        let index = (range.start >> (12 + 9 * level)) & 511;
        let pte = unsafe {
            MockKernel::pa_to_va(page)
                .as_mut_ptr::<paging::entry::PTEntry<X86Paging<Platform<MockKernel>>>>()
                .add(index)
        };
        let entry = unsafe { load_entry(pte) };
        let original = entry.raw();
        for restricted in [
            original & !(PageTableFlags::WRITABLE.bits() as usize),
            original & !(PageTableFlags::USER_ACCESSIBLE.bits() as usize),
            original | PageTableFlags::NO_EXECUTE.bits() as usize,
        ] {
            unsafe { &*pte.cast::<AtomicUsize>() }.store(restricted, Ordering::Release);
            let before = crate::mm::tests::effective_flags(root, range.start);
            let flush_start = FLUSHES.lock().len();
            assert!(std::panic::catch_unwind(|| unsafe { MockTable::init(root) }).is_err());
            assert_eq!(unsafe { load_entry(pte) }.raw(), restricted);
            assert_eq!(crate::mm::tests::effective_flags(root, range.start), before);
            assert_eq!(FLUSHES.lock().len(), flush_start);
            unsafe { &*pte.cast::<AtomicUsize>() }.store(entry.raw(), Ordering::Release);
        }
        page = PhysAddr::new(entry.address() as u64);
    }
    let table = unsafe { MockTable::init(root) };
    unsafe { table.unmap_pages(range, true) }.unwrap();
}

#[test]
fn boot_import_preserves_restrictive_kernel_subtrees_and_rejects_user_faults_there() {
    let table = table();
    let root = PhysAddr::new(table.inner.lock().root_paddr().bits() as u64);
    let user = PageRange::new(0xa0_0000, 0xa0_1000).unwrap();
    table.map_pages(user, VmFlags::VM_READ, true);
    let kernel_address = 0xffff_9000_0000_1000usize;
    let data = MockKernel::mem_allocate_pages(0).unwrap();
    let physical = MockKernel::va_to_pa(VirtAddr::new(data as u64));
    table
        .inner
        .lock()
        .map_with_parent_flags(
            paging::page::Page::<paging::sizes::Regular>::from_start_address(
                kernel_address.into(),
            )
            .unwrap(),
            paging::frame::PhysFrame::<paging::sizes::Regular>::from_start_address(
                (physical.as_u64() as usize).into(),
            )
            .unwrap(),
            PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER,
            false,
            paging_flags(PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE),
        )
        .unwrap();
    let kernel_ancestors = ancestor_words(&table, kernel_address);
    let kernel_leaf = permissions(&table, kernel_address);
    assert_eq!(
        effective_permissions(&table, kernel_address),
        PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE
    );
    drop(table);
    let table = unsafe { MockTable::init(root) };
    unsafe { table.mprotect_pages(user, VmFlags::VM_READ | VmFlags::VM_EXEC) }.unwrap();
    assert_eq!(ancestor_words(&table, kernel_address), kernel_ancestors);
    assert_eq!(permissions(&table, kernel_address), kernel_leaf);
    assert_eq!(
        effective_permissions(&table, kernel_address),
        PageTableFlags::PRESENT | PageTableFlags::NO_EXECUTE
    );
    assert!(matches!(
        unsafe {
            PageTableImpl::handle_page_fault(
                &table,
                Page::from_start_address(VirtAddr::new(kernel_address as u64)).unwrap(),
                vmflags_to_pteflags(VmFlags::VM_READ | VmFlags::VM_WRITE),
                PageFaultErrorCode::empty(),
            )
        },
        Err(PageFaultError::AccessError("kernel address is not a user mapping"))
    ));
    unsafe { table.unmap_pages(user, true) }.unwrap();
    let (_, flush) = table
        .inner
        .lock()
        .unmap(
            paging::page::Page::<paging::sizes::Regular>::from_start_address(
                kernel_address.into(),
            )
            .unwrap(),
            Some(FLUSH_ALL_CPUS),
        )
        .unwrap();
    flush_local::<MockKernel>(flush);
    unsafe { MockKernel::mem_free_pages(data, 0) };
}

#[test]
fn range_split_postflush_holds_whole_content_domain() {
    let table = table();
    let address = PagingVirtAddr::from(0x6000_0000usize);
    let flags = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER;
    let inner = table.inner.lock();
    inner
        .map(
            paging::page::Page::<paging::sizes::Huge>::from_start_address(address).unwrap(),
            paging::frame::PhysFrame::<paging::sizes::Huge>::from_start_address(
                0x5000_0000usize.into(),
            )
            .unwrap(),
            flags,
            false,
        )
        .unwrap();
    let protected = address + 4096;
    let observation = observe_transition(&inner, protected);
    let (result, flush) = inner.set_flags_range(
        protected,
        protected + 4096,
        flags - PTEntryFlags::WRITABLE,
        FLUSH_ALL_CPUS,
    );
    result.unwrap();
    flush.expect_no_flush();
    assert_eq!(TRANSITION_FLUSHES.with(Cell::get), 1);
    drop(observation);
    drop(inner);
    assert_eq!(
        effective_permissions(&table, protected.bits()),
        PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE
    );
    for neighbor in [address, address + 8192] {
        assert_eq!(
            effective_permissions(&table, neighbor.bits()),
            PageTableFlags::PRESENT | PageTableFlags::USER_ACCESSIBLE | PageTableFlags::WRITABLE
        );
    }
    flush_local::<MockKernel>(
        table.inner.lock().unmap_region(address, address + 2 * 1024 * 1024).unwrap().1,
    );
}

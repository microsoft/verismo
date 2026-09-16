extern crate alloc;
extern crate std;

use super::*;
use crate::cpu::TlbFlushRange;
use crate::mm::alloc::{memory_info, TestRootMem, DEFAULT_TEST_MEMORY_SIZE};
use crate::mm::pagetable::paging_init;
use crate::platform::init_platform_type;
use crate::platform::native::NativePlatform;
use bootdefs::platform::SvsmPlatformType;
use core::cell::RefCell;
use paging::pagetable::{MappingMutOps as _, MappingRefOps as _};

type Entry = verismo_paging::entry::PTEntry<Architecture>;

struct EntryProbe {
    slot: *const Entry,
    level: PageLevel,
}

struct TransitionFlushProbe {
    scope: TlbFlushScope,
    entries: alloc::vec::Vec<EntryProbe>,
    calls: usize,
}

std::thread_local! {
    static TRANSITION_FLUSH: RefCell<Option<TransitionFlushProbe>> = const { RefCell::new(None) };
}

fn assert_scope(actual: TlbFlushScope, expected: TlbFlushScope) {
    assert_eq!(actual.global, expected.global);
    match (actual.range, expected.range) {
        (TlbFlushRange::All, TlbFlushRange::All) => {}
        (
            TlbFlushRange::Range { region, pgsize },
            TlbFlushRange::Range { region: expected_region, pgsize: expected_size },
        ) => {
            assert_eq!(region.start(), expected_region.start());
            assert_eq!(region.len(), expected_region.len());
            assert_eq!(pgsize, expected_size);
        }
        _ => panic!("Unexpected TLB scope: {actual:?}, expected {expected:?}"),
    }
}

pub(super) fn record_transition_flush(scope: TlbFlushScope, all_cpus: bool) {
    assert!(all_cpus, "SVSM mappings have no CPU-local ownership guarantee");
    TRANSITION_FLUSH.with(|state| {
        let mut state = state.borrow_mut();
        let probe = state.as_mut().expect("Unregistered synchronous host flush");
        assert_eq!(probe.calls, 0, "Expected one synchronous shootdown");
        assert_scope(scope, probe.scope);
        for entry in &probe.entries {
            // SAFETY: the scoped test operation keeps these native table pages
            // alive; observing the recorded slots does not reenter its controller.
            assert!(unsafe { Entry::load_entry(entry.slot) }.is_table(entry.level));
        }
        probe.calls += 1;
    });
}

struct TransitionFlushGuard;

impl Drop for TransitionFlushGuard {
    fn drop(&mut self) {
        TRANSITION_FLUSH.with(|state| {
            state.borrow_mut().take();
        });
    }
}

fn probe_huge_entry(table: &PageTable<'_>, va: VirtAddr) -> EntryProbe {
    let mut page = phys_to_virt(PhysAddr::from(table.inner.root_paddr().bits())).as_ptr::<Entry>();
    let mut level = PageLevel::Level3;
    loop {
        let index = verismo_paging::sizes::entry_index(va.bits().into(), level);
        // SAFETY: the validated test tree remains alive; each index is in the
        // current table page and the native allocator resolves every child page.
        let (slot, entry) = unsafe {
            let slot = page.add(index);
            (slot, Entry::load_entry(slot))
        };
        if entry.is_leaf(level) {
            assert_ne!(level, PageLevel::Level0);
            return EntryProbe { slot, level };
        }
        assert!(entry.is_table(level));
        page = phys_to_virt(PhysAddr::from(entry.address())).as_ptr::<Entry>();
        level = level.child().unwrap();
    }
}

fn with_transition_flush<R>(
    table: &mut PageTable<'_>,
    old_pages: &[VirtAddr],
    scope: TlbFlushScope,
    operation: impl FnOnce(&mut PageTable<'_>) -> R,
) -> R {
    let entries = old_pages.iter().map(|va| probe_huge_entry(table, *va)).collect();
    TRANSITION_FLUSH.with(|state| {
        let mut state = state.borrow_mut();
        assert!(state.is_none());
        *state = Some(TransitionFlushProbe { scope, entries, calls: 0 });
    });
    let _guard = TransitionFlushGuard;
    let result = operation(table);
    TRANSITION_FLUSH.with(|state| {
        let state = state.borrow();
        let probe = state.as_ref().unwrap();
        assert_eq!(probe.calls, 1, "Missing synchronous split flush");
        for entry in &probe.entries {
            // SAFETY: the test still owns the tree, including the recorded slots.
            assert!(unsafe { Entry::load_entry(entry.slot) }.is_table(entry.level));
        }
    });
    result
}

fn discard_unpublished(flush: Flush) {
    // SAFETY: no table in these tests was installed in hardware.
    unsafe { flush.ignore() };
}

fn expect_flush(flush: Flush, start: VirtAddr, size: usize, pgsize: PageSize) {
    assert!(flush.is_pending());
    assert_scope(
        flush.scope().unwrap(),
        TlbFlushScope::range(MemoryRegion::new(start, size), pgsize),
    );
    discard_unpublished(flush);
}

fn write_owned_private(
    table: &PageTable<'_>,
    va: VirtAddr,
    payload: &mut PageBox<[u8; 4096]>,
    value: u8,
) -> Result<(), PagingError> {
    if !table.owns_children {
        return Err(PagingError::InvalidFlags);
    }
    let mapping = table.mapping(va)?;
    if !mapping.flags.writable() {
        return Err(PagingError::InvalidFlags);
    }
    if (Architecture::private_pte_mask() | Architecture::shared_pte_mask()) != 0 && mapping.shared {
        return Err(PagingError::InvalidAddress);
    }
    let pa = table.phys_addr(va)?.bits();
    let base = virt_to_phys(payload.vaddr()).bits();
    let offset =
        pa.checked_sub(base).filter(|offset| *offset < 4096).ok_or(PagingError::InvalidAddress)?;
    payload[offset] = value;
    Ok(())
}

#[derive(Debug)]
struct NativeOwner(NativePageTable);

impl Drop for NativeOwner {
    fn drop(&mut self) {
        // SAFETY: these native test trees are unpublished and unaliased.
        unsafe {
            self.0.as_inactive().free_children();
            self.0.dealloc();
        }
    }
}

fn borrowed_native_tree() {
    let mut native = NativeOwner(NativePageTable::alloc().unwrap());
    let root = native.0.root_pa();
    let before_rejection = alloc::format!("{:?}", memory_info());
    // SAFETY: the fresh root is acyclic, exclusively owned and arena-mapped.
    let rejected = unsafe { PageTable::from_svsm(&mut native.0) }.unwrap_err();
    assert_eq!(rejected, PagingError::TablePageNotSelfMapped);
    assert_eq!(alloc::format!("{:?}", memory_info()), before_rejection);
    assert_eq!(native.0.root_pa(), root);

    let (pa, va, size) = crate::mm::alloc::root_memory_mapping();
    native.0.map_region_4k(va, va + size, pa, PTEntryFlags::data(), false).unwrap();
    let mapped = VirtAddr::from(0x9000_0000usize);
    let huge = PhysAddr::from(0x2800_0000usize);
    let adjacent = mapped + PageLevel::Level1.size();
    for address in [mapped, adjacent] {
        native.0.map_2m(address, huge, PTEntryFlags::data(), false).unwrap();
        let mut mapping = native.0.walk_mut(address);
        let mut entry = mapping.read();
        entry.set(PhysAddr::from(entry.paddr_field().bits() | (1 << 12)), entry.flags());
        *mapping.staged().entry = entry;
        // SAFETY: these native PAT-bearing entries have never been installed.
        unsafe { mapping.commit().ignore() };
    }
    let inherited_global = native.0.walk(mapped).read().flags().global();
    {
        // SAFETY: this native tree is acyclic, fully arena-mapped, unpublished
        // and inaccessible through its owner until the exclusive borrow ends.
        let mut borrowed = unsafe { PageTable::from_svsm(&mut native.0) }.unwrap();
        assert_eq!(borrowed.root_paddr(), root);
        with_transition_flush(
            &mut borrowed,
            &[mapped],
            TlbFlushScope::page(mapped, PageSize::Huge),
            |table| {
                table.mprotect(mapped + 4096, PageLevel::Level0, PTEntryFlags::data_ro()).unwrap()
            },
        )
        .expect_no_flush();
        let protected = borrowed.mapping(mapped + 4096).unwrap();
        assert_eq!(protected.frame, huge + 4096);
        assert_ne!(protected.flags.bits() & (1 << 7), 0);
        assert!(protected.flags.contains(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
        let flush =
            borrowed.mprotect(mapped + 8192, PageLevel::Level0, PTEntryFlags::data_ro()).unwrap();
        expect_flush(flush, mapped + 8192, 4096, PageSize::Regular);
        let protected = borrowed.mapping(mapped + 8192).unwrap();
        assert_eq!(protected.frame, huge + 8192);
        assert_ne!(protected.flags.bits() & (1 << 7), 0);
        assert!(protected.flags.contains(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
        let flush =
            borrowed.mprotect(adjacent, PageLevel::Level1, PTEntryFlags::data_ro()).unwrap();
        expect_flush(flush, adjacent, PageLevel::Level1.size(), PageSize::Huge);
        assert_ne!(borrowed.inner.walk(adjacent.bits().into()).read().raw() & (1 << 12), 0);
        let (old_huge, flush) = borrowed.unmap(adjacent, PageLevel::Level1).unwrap();
        let old_huge = old_huge.unwrap();
        assert_eq!(old_huge.frame, huge);
        assert!(!old_huge.flags.writable());
        assert!(old_huge.flags.contains(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
        expect_flush(flush, adjacent, PageLevel::Level1.size(), PageSize::Huge);
    }
    assert_eq!(native.0.root_pa(), root);
    assert_eq!(native.0.phys_addr(mapped + 8192).unwrap(), huge + 8192);
    assert!(!native.0.walk(mapped + 4096).read().flags().writable());
    assert!(!native.0.walk(mapped + 8192).read().flags().writable());
    assert!(!native.0.walk(adjacent).read().present());
    assert!(native.0.walk(mapped).read().flags().writable());
    assert_eq!(native.0.walk(mapped).read().flags().global(), inherited_global);

    // SAFETY: the tree remains unpublished and is accessed only here.
    unsafe { native.0.as_inactive().init_self_map(root) };
    // SAFETY: the only cycle is the standard recursive slot, which is rejected.
    let rejected = unsafe { PageTable::from_svsm(&mut native.0) }.unwrap_err();
    let slot = native.0.root_vaddr().as_mut_ptr::<usize>();
    // SAFETY: remove exactly the recursive entry just inserted, before teardown.
    unsafe { slot.add(crate::mm::PGTABLE_LVL3_IDX_PTE_SELFMAP).write(0) };
    assert_eq!(rejected, PagingError::InvalidAddress);
}

fn borrowed_huge_arena_allows_x86_neighbor_splits() {
    let mut native = NativeOwner(NativePageTable::alloc().unwrap());
    let (pa, va, size) = crate::mm::alloc::root_memory_mapping();
    let arena_end = va + size;
    let huge_start = va.align_down(PageLevel::Level1.size());
    let huge_end = arena_end.align_up(PageLevel::Level1.size());
    let map_start = huge_start - PageLevel::Level1.size();
    let map_end = huge_end + PageLevel::Level1.size();
    native
        .0
        .map_region_2m(map_start, map_end, pa - (va - map_start), PTEntryFlags::data(), false)
        .unwrap();
    let mut neighbors = alloc::vec::Vec::new();
    if huge_start < va {
        neighbors.push(va - 4096);
    }
    if arena_end < huge_end {
        neighbors.push(arena_end);
    }
    assert!(!neighbors.is_empty());
    let root = native.0.root_pa();
    {
        // SAFETY: the native tree is acyclic, privately arena-mapped and unpublished.
        let mut borrowed = unsafe { PageTable::from_svsm(&mut native.0) }.unwrap();
        for neighbor in neighbors {
            borrowed.check_range(neighbor.bits(), 4096).unwrap();
            let physical = borrowed.phys_addr(neighbor).unwrap();
            with_transition_flush(
                &mut borrowed,
                &[neighbor],
                TlbFlushScope::page(neighbor.align_down(PageLevel::Level1.size()), PageSize::Huge),
                |table| table.split(neighbor, PageLevel::Level0).unwrap().expect_no_flush(),
            );
            assert_eq!(borrowed.mapping(neighbor).unwrap().level, PageLevel::Level0);
            assert_eq!(borrowed.phys_addr(neighbor).unwrap(), physical);
            assert_eq!(borrowed.phys_addr(phys_to_virt(root)).unwrap(), root);
        }
        borrowed.inner.validate_page_table().unwrap();
    }
}

#[test]
fn actual_svsm_allocator_and_kernel_types() {
    init_platform_type(SvsmPlatformType::Native);
    let suppress_global = std::env::var_os("SVSM_VERISMO_SUPPRESS_GLOBAL").is_some();
    paging_init(&NativePlatform {}, suppress_global).unwrap();
    // The extra page ensures an arena edge lies inside, rather than between, huge leaves.
    let _arena = TestRootMem::setup(DEFAULT_TEST_MEMORY_SIZE + 4096);
    let free_before = alloc::format!("{:?}", memory_info());
    {
        let (physical, virtual_base) = Allocator::root_memory().unwrap();
        assert_eq!(Allocator::direct_map(), (physical, virtual_base));
        assert_eq!(alloc::format!("{:?}", memory_info()), free_before);
        let frame = Allocator::allocate_table_page().unwrap();
        assert_ne!(alloc::format!("{:?}", memory_info()), free_before);
        // SAFETY: the frame was never published.
        unsafe { Allocator::deallocate_table_page(frame) };
        assert_eq!(alloc::format!("{:?}", memory_info()), free_before);
    }
    {
        // SAFETY: the SVSM memory guard outlives the unpublished table.
        let mut table = unsafe { PageTable::new() }.unwrap();
        assert_ne!(alloc::format!("{:?}", memory_info()), free_before);
        table.inner.validate_page_table().unwrap();
        let root_va = phys_to_virt(table.root_paddr());
        assert_eq!(table.phys_addr(root_va).unwrap(), table.root_paddr());
        let self_map = table.mapping(root_va).unwrap();
        assert!(self_map.flags.writable());
        assert!(self_map.flags.nx());
        assert_eq!(self_map.flags.global(), !suppress_global);
        assert!(!self_map.flags.contains(PTEntryFlags::USER));

        let va = VirtAddr::from(0x4000_0000usize);
        let huge_pa = PhysAddr::from(0x2000_0000usize);
        table.map(va, huge_pa, PageLevel::Level1, PTEntryFlags::data(), false).unwrap();
        assert_eq!(table.mapping(va).unwrap().flags.global(), !suppress_global);
        assert_eq!(table.phys_addr(va + 0x12345).unwrap(), huge_pa + 0x12345);
        assert!(matches!(
            table.map(va, huge_pa, PageLevel::Level1, PTEntryFlags::data(), false),
            Err(PagingError::EntryAlreadyPresent { .. })
        ));

        let page = va + 4096;
        with_transition_flush(
            &mut table,
            &[va],
            TlbFlushScope::page(va, PageSize::Huge),
            |table| table.mprotect(page, PageLevel::Level0, PTEntryFlags::data_ro()).unwrap(),
        )
        .expect_no_flush();
        let readonly = table.mapping(page).unwrap();
        assert_eq!(readonly.frame, huge_pa + 4096);
        assert_eq!(readonly.level, PageLevel::Level0);
        assert_eq!(readonly.flags.global(), !suppress_global);
        assert!(!readonly.flags.writable());
        assert!(readonly.flags.nx());
        assert!(table.mapping(va).unwrap().flags.writable());
        assert!(table.mapping(page + 4096).unwrap().flags.writable());
        assert_eq!(table.mapping(va).unwrap().level, PageLevel::Level0);

        table.split(va, PageLevel::Level0).unwrap().expect_no_flush();
        let mut payload = PageBox::<[u8; 4096]>::try_new_zeroed().unwrap();
        let payload_pa = virt_to_phys(payload.vaddr());
        let payload_va = va + PageLevel::Level1.size();
        table.map(payload_va, payload_pa, PageLevel::Level0, PTEntryFlags::data(), false).unwrap();
        assert_eq!(table.phys_addr(payload_va + 27).unwrap(), payload_pa + 27);
        assert!(table.mapping(payload_va).unwrap().flags.writable());
        assert_eq!(table.mapping(payload_va).unwrap().flags.global(), !suppress_global);
        write_owned_private(&table, payload_va + 27, &mut payload, 0xa5).unwrap();
        assert_eq!(payload[27], 0xa5);
        assert_eq!(
            write_owned_private(&table, va + 27, &mut payload, 0xff),
            Err(PagingError::InvalidAddress),
        );

        let range = MemoryRegion::new(payload_va - 8192, 3 * 4096);
        let (result, flush) = table.mprotect_range(range, PTEntryFlags::data_ro());
        result.unwrap();
        expect_flush(flush, range.start(), range.len(), PageSize::Regular);
        for page in range.iter_pages(PageSize::Regular) {
            assert!(!table.mapping(page).unwrap().flags.writable());
        }
        let payload_readonly = table.mapping(payload_va).unwrap();
        assert_eq!(
            write_owned_private(&table, payload_va + 27, &mut payload, 0xff),
            Err(PagingError::InvalidFlags),
        );
        assert_eq!(payload[27], 0xa5);

        let missing = VirtAddr::from(0x5000_0000usize);
        table.map(missing, payload_pa, PageLevel::Level0, PTEntryFlags::data(), false).unwrap();
        let (result, flush) =
            table.mprotect_range(MemoryRegion::new(missing, 8192), PTEntryFlags::data_ro());
        assert_eq!(result, Err(PagingError::NotMapped));
        expect_flush(flush, missing, 4096, PageSize::Regular);
        assert!(!table.mapping(missing).unwrap().flags.writable());

        let before_invalid = table.mapping(page).unwrap();
        assert!(matches!(
            table.map(
                payload_va + 4096,
                payload_pa + 1,
                PageLevel::Level0,
                PTEntryFlags::data(),
                false
            ),
            Err(PagingError::InvalidAddress)
        ));
        assert_eq!(table.phys_addr(payload_va + 4096), Err(PagingError::NotMapped));
        assert_eq!(
            table.mprotect(page, PageLevel::Level0, PTEntryFlags::empty()).unwrap_err(),
            PagingError::InvalidFlags,
        );
        assert_eq!(
            table
                .mprotect(
                    page,
                    PageLevel::Level0,
                    PTEntryFlags::from_bits_retain(PTEntryFlags::data().bits() | (1 << 40))
                )
                .unwrap_err(),
            PagingError::InvalidFlags,
        );
        assert_eq!(table.mapping(page).unwrap(), before_invalid);
        assert!(matches!(
            table.mprotect(va, PageLevel::Level1, PTEntryFlags::data_ro()),
            Err(PagingError::NotLeafEntry)
        ));
        assert_eq!(
            table.mprotect(root_va, PageLevel::Level0, PTEntryFlags::data_ro()).unwrap_err(),
            PagingError::InvalidAddress,
        );
        assert_eq!(table.phys_addr(root_va).unwrap(), table.root_paddr());

        let huge = VirtAddr::from(0x6000_0000usize);
        table.map(huge, huge_pa, PageLevel::Level1, PTEntryFlags::data(), false).unwrap();
        with_transition_flush(
            &mut table,
            &[huge],
            TlbFlushScope::page(huge, PageSize::Huge),
            |table| table.split(huge, PageLevel::Level0).unwrap(),
        )
        .expect_no_flush();
        assert_eq!(table.phys_addr(huge + 0x1ff123).unwrap(), huge_pa + 0x1ff123);

        let gigantic = VirtAddr::from(0x1_4000_0000usize);
        let gigantic_pa = PhysAddr::from(0x4000_0000usize);
        table.map(gigantic, gigantic_pa, PageLevel::Level2, PTEntryFlags::data(), false).unwrap();
        let before_gigantic = table.mapping(gigantic).unwrap();

        let exhausted = VirtAddr::from(0x7000_0000usize);
        table.map(exhausted, huge_pa, PageLevel::Level1, PTEntryFlags::data(), false).unwrap();
        let before_exhaustion = table.mapping(exhausted).unwrap();
        let mut held = alloc::vec::Vec::new();
        loop {
            match PageBox::<[u8; 4096]>::try_new_zeroed() {
                Ok(page) => held.push(page),
                Err(crate::error::SvsmError::Alloc(crate::mm::alloc::AllocError::OutOfMemory)) => {
                    break;
                }
                Err(error) => panic!("Unexpected allocator error: {error:?}"),
            }
        }
        assert_eq!(
            table
                .mprotect(exhausted + 4096, PageLevel::Level0, PTEntryFlags::data_ro())
                .unwrap_err(),
            PagingError::AllocFrame,
        );
        assert_eq!(table.mapping(exhausted).unwrap(), before_exhaustion);
        // A 1 GiB-to-4 KiB split needs two child pages; make only one available.
        drop(held.pop().unwrap());
        let before_partial_allocation = alloc::format!("{:?}", memory_info());
        assert_eq!(
            table
                .mprotect(gigantic + 4096, PageLevel::Level0, PTEntryFlags::data_ro())
                .unwrap_err(),
            PagingError::AllocFrame,
        );
        assert_eq!(table.mapping(gigantic).unwrap(), before_gigantic);
        assert_eq!(alloc::format!("{:?}", memory_info()), before_partial_allocation);
        drop(held);
        with_transition_flush(
            &mut table,
            &[exhausted],
            TlbFlushScope::page(exhausted, PageSize::Huge),
            |table| {
                table
                    .mprotect(exhausted + 4096, PageLevel::Level0, PTEntryFlags::data_ro())
                    .unwrap()
            },
        )
        .expect_no_flush();

        with_transition_flush(&mut table, &[gigantic], TlbFlushScope::all(), |table| {
            table.split(gigantic, PageLevel::Level0).unwrap()
        })
        .expect_no_flush();
        assert_eq!(
            table.phys_addr(gigantic + PageLevel::Level2.size() - 1).unwrap(),
            gigantic_pa + PageLevel::Level2.size() - 1,
        );

        let ranged_huge = VirtAddr::from(0x7600_0000usize);
        table.map(ranged_huge, huge_pa, PageLevel::Level1, PTEntryFlags::data(), false).unwrap();
        let last_page = ranged_huge + PageLevel::Level1.size() - 4096;
        let (result, flush) = with_transition_flush(
            &mut table,
            &[ranged_huge],
            TlbFlushScope::page(ranged_huge, PageSize::Huge),
            |table| {
                table.mprotect_range(MemoryRegion::new(last_page, 8192), PTEntryFlags::data_ro())
            },
        );
        assert_eq!(result, Err(PagingError::NotMapped));
        flush.expect_no_flush();
        assert!(!table.mapping(last_page).unwrap().flags.writable());
        assert!(table.mapping(last_page - 4096).unwrap().flags.writable());

        let (removed, flush) = table.unmap(payload_va, PageLevel::Level0).unwrap();
        assert_eq!(removed.unwrap(), payload_readonly);
        expect_flush(flush, payload_va, 4096, PageSize::Regular);
        assert_eq!(table.phys_addr(payload_va), Err(PagingError::NotMapped));
        assert_eq!(
            write_owned_private(&table, payload_va + 27, &mut payload, 0xff),
            Err(PagingError::NotMapped),
        );
        let (removed, flush) = table.unmap(payload_va, PageLevel::Level0).unwrap();
        assert!(removed.is_none());
        discard_unpublished(flush);
        table.inner.validate_page_table().unwrap();
    }
    borrowed_native_tree();
    borrowed_huge_arena_allows_x86_neighbor_splits();
    assert_eq!(alloc::format!("{:?}", memory_info()), free_before);
}

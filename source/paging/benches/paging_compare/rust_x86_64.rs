use std::mem::size_of;
use std::sync::{Arc, Mutex};

use x86_64::structures::paging::mapper::{
    MappedPageTable, Mapper, PageTableFrameMapping, Translate, TranslateResult,
};
use x86_64::structures::paging::{
    FrameAllocator, Page, PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB, Size4KiB,
};
use x86_64::{PhysAddr, VirtAddr};

use super::common::{
    Arena, ControllerMemory, MemorySnapshot, Observation, PagingAdapter, PAGE_SIZE,
};

#[derive(Clone, Copy)]
/// Identity frame mapping for arena-backed page tables.
struct ArenaMapping;

// SAFETY: every table frame is an arena pointer kept alive by RustX86Adapter.
unsafe impl PageTableFrameMapping for ArenaMapping {
    fn frame_to_pointer(&self, frame: PhysFrame) -> *mut PageTable {
        frame.start_address().as_u64() as *mut PageTable
    }
}

/// Frame allocator wrapper consumed by x86_64 mapping operations.
struct ArenaFrames(Arc<Arena>);

// SAFETY: the arena returns unique aligned frames backed for the adapter lifetime.
unsafe impl FrameAllocator<Size4KiB> for ArenaFrames {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        let address = self.0.allocate_page()? as u64;
        PhysFrame::from_start_address(PhysAddr::new(address)).ok()
    }
}

/// Concrete x86_64 mapper type using arena identity mapping.
type MapperType = MappedPageTable<'static, ArenaMapping>;

/// Rust x86_64 crate implementation under test.
pub struct RustX86Adapter {
    mapper: Mutex<MapperType>,
    arena: Arc<Arena>,
}

fn flags(writable: bool) -> PageTableFlags {
    let flags = PageTableFlags::PRESENT
        | PageTableFlags::USER_ACCESSIBLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::ACCESSED;
    if writable {
        flags | PageTableFlags::WRITABLE | PageTableFlags::DIRTY
    } else {
        flags
    }
}

impl RustX86Adapter {
    fn with_mapper<R>(&self, operation: impl FnOnce(&mut MapperType) -> R) -> R {
        operation(&mut self.mapper.lock().unwrap())
    }

    fn split(mapper: &mut MapperType, arena: &Arc<Arena>, virtual_address: u64) {
        let address = VirtAddr::new(virtual_address);
        let p4 = mapper.level_4_table_mut();
        let p3_entry = &mut p4[address.p4_index()];
        assert!(p3_entry.flags().contains(PageTableFlags::PRESENT));
        // SAFETY: arena frame mapping keeps every present table address live and aligned.
        let p3 = unsafe { &mut *(p3_entry.addr().as_u64() as *mut PageTable) };
        let p2_entry = &mut p3[address.p3_index()];
        assert!(p2_entry.flags().contains(PageTableFlags::PRESENT));
        // SAFETY: arena frame mapping keeps every present table address live and aligned.
        let p2 = unsafe { &mut *(p2_entry.addr().as_u64() as *mut PageTable) };
        let leaf = &mut p2[address.p2_index()];
        let old_flags = leaf.flags();
        assert!(old_flags.contains(PageTableFlags::PRESENT | PageTableFlags::HUGE_PAGE));
        let physical_base = leaf.addr().align_down(Size2MiB::SIZE);
        let child_address = arena.allocate_page().expect("x86_64 split table");
        // SAFETY: this fresh aligned arena page is exclusively owned and zeroed.
        let child = unsafe { &mut *(child_address as *mut PageTable) };
        let child_flags = old_flags - PageTableFlags::HUGE_PAGE;
        for (index, entry) in child.iter_mut().enumerate() {
            let frame =
                PhysFrame::<Size4KiB>::from_start_address(physical_base + index as u64 * PAGE_SIZE)
                    .expect("split frame");
            entry.set_frame(frame, child_flags);
        }
        let child_frame =
            PhysFrame::<Size4KiB>::from_start_address(PhysAddr::new(child_address as u64))
                .expect("split table frame");
        let parent_flags = old_flags
            & (PageTableFlags::PRESENT
                | PageTableFlags::WRITABLE
                | PageTableFlags::USER_ACCESSIBLE
                | PageTableFlags::WRITE_THROUGH
                | PageTableFlags::NO_CACHE
                | PageTableFlags::ACCESSED
                | PageTableFlags::NO_EXECUTE);
        leaf.set_frame(child_frame, parent_flags);
    }
}

impl PagingAdapter for RustX86Adapter {
    const NAME: &'static str = "x86_64-0.15.2";

    fn new(arena_pages: usize) -> Self {
        let arena = Arena::new(arena_pages);
        let root = arena.allocate_page().expect("x86_64 root") as *mut PageTable;
        // SAFETY: the root allocation is aligned, zeroed, and retained by `arena`.
        let root: &'static mut PageTable = unsafe { &mut *root };
        // SAFETY: ArenaMapping resolves every allocated frame for the mapper's lifetime.
        let mapper = unsafe { MappedPageTable::new(root, ArenaMapping) };
        Self { mapper: Mutex::new(mapper), arena }
    }

    fn map_4k(&self, virtual_address: u64, physical_address: u64) {
        let arena = self.arena.clone();
        self.with_mapper(|mapper| {
            let page =
                Page::<Size4KiB>::from_start_address(VirtAddr::new(virtual_address)).unwrap();
            let frame =
                PhysFrame::<Size4KiB>::from_start_address(PhysAddr::new(physical_address)).unwrap();
            let mut frames = ArenaFrames(arena);
            // SAFETY: the synthetic page and frame are unused and remain arena-backed.
            unsafe { mapper.map_to(page, frame, flags(true), &mut frames) }
                .expect("x86_64 map_4k")
                .ignore();
        });
    }

    fn map_2m(&self, virtual_address: u64, physical_address: u64) {
        let arena = self.arena.clone();
        self.with_mapper(|mapper| {
            let page =
                Page::<Size2MiB>::from_start_address(VirtAddr::new(virtual_address)).unwrap();
            let frame =
                PhysFrame::<Size2MiB>::from_start_address(PhysAddr::new(physical_address)).unwrap();
            let mut frames = ArenaFrames(arena);
            // SAFETY: the synthetic page and frame are unused and remain arena-backed.
            unsafe { mapper.map_to(page, frame, flags(true), &mut frames) }
                .expect("x86_64 map_2m")
                .ignore();
        });
    }

    fn unmap_4k(&self, virtual_address: u64) {
        self.with_mapper(|mapper| {
            let page =
                Page::<Size4KiB>::from_start_address(VirtAddr::new(virtual_address)).unwrap();
            mapper.unmap(page).expect("x86_64 unmap").1.ignore();
        });
    }

    fn translate(&self, virtual_address: u64) -> Option<u64> {
        self.with_mapper(|mapper| match mapper.translate(VirtAddr::new(virtual_address)) {
            TranslateResult::Mapped { frame, offset, .. } => {
                Some(frame.start_address().as_u64() + offset)
            }
            TranslateResult::NotMapped | TranslateResult::InvalidFrameAddress(_) => None,
        })
    }

    fn observe(&self, virtual_address: u64) -> Option<Observation> {
        self.with_mapper(|mapper| match mapper.translate(VirtAddr::new(virtual_address)) {
            TranslateResult::Mapped { frame, offset, flags } => Some(Observation {
                physical: frame.start_address().as_u64() + offset,
                page_size: frame.size(),
                writable: flags.contains(PageTableFlags::WRITABLE),
                user: flags.contains(PageTableFlags::USER_ACCESSIBLE),
                executable: !flags.contains(PageTableFlags::NO_EXECUTE),
            }),
            TranslateResult::NotMapped | TranslateResult::InvalidFrameAddress(_) => None,
        })
    }

    fn protect_4k(&self, virtual_address: u64, writable: bool) {
        self.with_mapper(|mapper| {
            let page =
                Page::<Size4KiB>::from_start_address(VirtAddr::new(virtual_address)).unwrap();
            // SAFETY: setup created this mapping and the mapper mutex excludes other mutations.
            unsafe { mapper.update_flags(page, flags(writable)) }
                .expect("x86_64 update_flags")
                .ignore();
        });
    }

    fn split_2m_to_4k(&self, virtual_address: u64) {
        let arena = self.arena.clone();
        self.with_mapper(|mapper| Self::split(mapper, &arena, virtual_address));
    }

    fn protect_range(&self, start: u64, end: u64, writable: bool) {
        self.with_mapper(|mapper| {
            let mut address = start;
            while address < end {
                let page = Page::<Size4KiB>::from_start_address(VirtAddr::new(address)).unwrap();
                // SAFETY: setup created this mapping and the mapper mutex excludes other mutations.
                unsafe { mapper.update_flags(page, flags(writable)) }
                    .expect("x86_64 range update_flags")
                    .ignore();
                address += PAGE_SIZE;
            }
        });
    }

    fn reset_peak(&self) {
        self.arena.reset_peak();
    }

    fn memory(&self) -> MemorySnapshot {
        self.arena.memory()
    }

    fn controller_memory(&self) -> ControllerMemory {
        ControllerMemory { inline_bytes: size_of::<Self>(), auxiliary_bytes: 0 }
    }
}

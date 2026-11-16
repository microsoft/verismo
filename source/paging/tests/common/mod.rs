//! A page table over host memory, so the tests can walk a real tree.
//!
//! The arena is a leaked, 2 MiB-aligned buffer, and the allocator direct-maps it
//! identically: a physical address in it is a host address the walk can
//! dereference. Allocator providers are stateless, so one arena is active at a
//! time within each test binary.
//!
//! Run them on a target that can execute:
//! `cargo test -p verios-pagetable-beta --target x86_64-unknown-linux-gnu`.
#![allow(dead_code)]

use std::cell::Cell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::ops::Range;
use std::prelude::rust_2021::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::{thread_local, vec};

use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    pagetable::{KernelPageTable, PageTable},
    structs::{
        ArchPagingMeta, DirectMappedAllocator, Huge, Lvl, PTEntry, Page, PageSize, PagingError,
        PagingOwnershipPolicy, PhysFrame, Regular, SizeLevel2, WalkLevel,
    },
    tlb::MayNeedFlush,
};

#[cfg(feature = "lock-wait-hook")]
#[no_mangle]
extern "C" fn paging_lock_wait() {}

pub fn page_4k(address: VirtAddr) -> Page<Regular> {
    Page::<Regular>::from_start_address(address).unwrap()
}

pub fn frame_4k(address: PhysAddr) -> PhysFrame<Regular> {
    PhysFrame::<Regular>::from_start_address(address).unwrap()
}

pub fn page_2m(address: VirtAddr) -> Page<Huge> {
    Page::<Huge>::from_start_address(address).unwrap()
}

pub fn frame_2m(address: PhysAddr) -> PhysFrame<Huge> {
    PhysFrame::<Huge>::from_start_address(address).unwrap()
}

pub fn page_1g(address: VirtAddr) -> Page<SizeLevel2> {
    Page::<SizeLevel2>::from_start_address(address).unwrap()
}

pub fn frame_1g(address: PhysAddr) -> PhysFrame<SizeLevel2> {
    PhysFrame::<SizeLevel2>::from_start_address(address).unwrap()
}

pub fn range_4k(start: VirtAddr, end: VirtAddr) -> paging::structs::PageRangeInclusive<Regular> {
    let start = Page::containing_address(start);
    let end = if start.start_address() < end {
        Page::containing_address(end - Regular::SIZE)
    } else {
        Page::containing_address(end)
    };
    Page::range_inclusive(start, end)
}

pub fn reclaim_range<Arch, Alloc, MaxLevel, Owned>(
    table: &mut PageTable<Arch, Alloc, MaxLevel, Owned>,
    start: VirtAddr,
    end: VirtAddr,
) where
    Arch: ArchPagingMeta,
    Alloc: paging::structs::PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy,
{
    if start == end {
        return;
    }
    table.cleanup_page_tables_by_range(start, end, MayNeedFlush::none());
}

pub fn reclaim_path<Arch, Alloc, MaxLevel, Owned>(
    table: &mut PageTable<Arch, Alloc, MaxLevel, Owned>,
    address: VirtAddr,
) -> usize
where
    Arch: ArchPagingMeta,
    Alloc: paging::structs::PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy,
{
    table.free_page_table_by_addr(address, MayNeedFlush::none())
}

pub fn contiguous_frames_4k(
    start: PhysAddr,
    pages: usize,
) -> impl Iterator<Item = PhysFrame<Regular>> {
    (0..pages).map(move |offset| frame_4k(start + offset * Regular::SIZE))
}

#[macro_export]
macro_rules! map_region_4k {
    ($table:expr, $start:expr, $end:expr, $frame:expr, $flags:expr) => {{
        let range = common::range_4k($start, $end);
        let mut frames = common::contiguous_frames_4k($frame, range.len());
        $table.map_region(range, &mut frames, $flags)
    }};
}

#[macro_export]
macro_rules! map_at {
    ($table:expr, $address:expr, $frame:expr, $level:expr, $flags:expr, $shared:expr) => {{
        match $level {
            paging::structs::PageLevel::Level0 => $table.map(
                paging::structs::Page::<paging::structs::Regular>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::Regular>::from_start_address($frame)
                    .unwrap(),
                $flags,
                $shared,
            ),
            paging::structs::PageLevel::Level1 => $table.map(
                paging::structs::Page::<paging::structs::Huge>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::Huge>::from_start_address($frame)
                    .unwrap(),
                $flags,
                $shared,
            ),
            paging::structs::PageLevel::Level2 => $table.map(
                paging::structs::Page::<paging::structs::SizeLevel2>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::SizeLevel2>::from_start_address(
                    $frame,
                )
                .unwrap(),
                $flags,
                $shared,
            ),
            _ => Err(paging::structs::PagingError::InvalidLevel),
        }
    }};
}

#[macro_export]
macro_rules! map_at_with_parent_flags {
    (
        $table:expr,
        $address:expr,
        $frame:expr,
        $level:expr,
        $flags:expr,
        $shared:expr,
        $parent_flags:expr
    ) => {{
        match $level {
            paging::structs::PageLevel::Level0 => $table.map_with_parent_flags(
                paging::structs::Page::<paging::structs::Regular>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::Regular>::from_start_address($frame)
                    .unwrap(),
                $flags,
                $shared,
                $parent_flags,
            ),
            paging::structs::PageLevel::Level1 => $table.map_with_parent_flags(
                paging::structs::Page::<paging::structs::Huge>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::Huge>::from_start_address($frame)
                    .unwrap(),
                $flags,
                $shared,
                $parent_flags,
            ),
            paging::structs::PageLevel::Level2 => $table.map_with_parent_flags(
                paging::structs::Page::<paging::structs::SizeLevel2>::from_start_address($address)
                    .unwrap(),
                paging::structs::PhysFrame::<paging::structs::SizeLevel2>::from_start_address(
                    $frame,
                )
                .unwrap(),
                $flags,
                $shared,
                $parent_flags,
            ),
            _ => Err(paging::structs::PagingError::InvalidLevel),
        }
    }};
}

#[macro_export]
macro_rules! unmap_at {
    ($table:expr, $address:expr, $level:expr) => {{
        match $level {
            paging::structs::PageLevel::Level0 => $table.unmap(
                paging::structs::Page::<paging::structs::Regular>::from_start_address($address)
                    .unwrap(),
                Some(true),
            ),
            paging::structs::PageLevel::Level1 => $table.unmap(
                paging::structs::Page::<paging::structs::Huge>::from_start_address($address)
                    .unwrap(),
                Some(true),
            ),
            paging::structs::PageLevel::Level2 => $table.unmap(
                paging::structs::Page::<paging::structs::SizeLevel2>::from_start_address($address)
                    .unwrap(),
                Some(true),
            ),
            _ => Err(paging::structs::PagingError::InvalidLevel),
        }
    }};
}

#[macro_export]
macro_rules! split_at {
    ($table:expr, $address:expr, $level:expr, $all_cpus:expr) => {{
        if $level == paging::structs::PageLevel::Level1 {
            $table.split(
                paging::structs::Page::<paging::structs::Huge>::containing_address($address),
                $all_cpus,
            )
        } else {
            Err(paging::structs::PagingError::InvalidLevel)
        }
    }};
}

#[macro_export]
macro_rules! set_flags_at {
    ($table:expr, $address:expr, $level:expr, $flags:expr, $all_cpus:expr) => {{
        match $level {
            paging::structs::PageLevel::Level0 => $table.set_flags(
                paging::structs::Page::<paging::structs::Regular>::from_start_address($address)
                    .unwrap(),
                $flags,
                $all_cpus,
            ),
            paging::structs::PageLevel::Level1 => $table.set_flags(
                paging::structs::Page::<paging::structs::Huge>::from_start_address($address)
                    .unwrap(),
                $flags,
                $all_cpus,
            ),
            paging::structs::PageLevel::Level2 => $table.set_flags(
                paging::structs::Page::<paging::structs::SizeLevel2>::from_start_address($address)
                    .unwrap(),
                $flags,
                $all_cpus,
            ),
            _ => Err(paging::structs::PagingError::InvalidLevel),
        }
    }};
}

pub unsafe fn entry_from_bits<A: ArchPagingMeta>(word: usize) -> PTEntry<A> {
    unsafe { (&word as *const usize).cast::<PTEntry<A>>().read() }
}

pub unsafe fn load_entry<A: ArchPagingMeta>(entry: *const PTEntry<A>) -> PTEntry<A> {
    let word = unsafe { AtomicUsize::from_ptr(entry.cast_mut().cast::<usize>()) };
    unsafe { entry_from_bits(word.load(Ordering::Acquire)) }
}

/// Unencrypted memory whose TLB needs no invalidating: the host's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Host;

thread_local! {
    static HOST_FLUSHES: Cell<usize> = const { Cell::new(0) };
}

pub fn host_flushes() -> usize {
    HOST_FLUSHES.with(Cell::get)
}

unsafe impl X86_64PagingParams for Host {
    fn private_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_scope: FlushScope) {
        HOST_FLUSHES.with(|count| count.set(count.get() + 1));
    }
}

/// A bump allocator over one leaked buffer, which remembers what was freed.
pub struct Arena {
    base: usize,
    len: usize,
    rebased_physical: AtomicUsize,
    state: Mutex<ArenaState>,
}

static ACTIVE_ARENA: Mutex<Option<usize>> = Mutex::new(None);
static ACTIVE_ARENA_CHANGED: Condvar = Condvar::new();

struct ArenaState {
    next: usize,
    live: BTreeSet<usize>,
    freed: Vec<usize>,
}

impl Arena {
    pub fn new(len: usize) -> Arc<Self> {
        assert!(len.is_power_of_two());
        let buf = vec![0u8; len * 2].leak();
        let base = (buf.as_mut_ptr() as usize + len - 1) & !(len - 1);
        let arena = Arc::new(Self {
            base,
            len,
            rebased_physical: AtomicUsize::new(base),
            state: Mutex::new(ArenaState { next: base, live: BTreeSet::new(), freed: Vec::new() }),
        });
        let mut active = ACTIVE_ARENA.lock().unwrap();
        while active.is_some() {
            active = ACTIVE_ARENA_CHANGED.wait(active).unwrap();
        }
        *active = Some(Arc::as_ptr(&arena) as usize);
        arena
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn rebase(&self, physical: usize) {
        self.rebased_physical.store(physical, Ordering::Relaxed);
    }

    /// How many pages have been handed out.
    pub fn allocated(&self) -> usize {
        (self.state.lock().unwrap().next - self.base) / 4096
    }

    pub fn freed(&self) -> Vec<usize> {
        self.state.lock().unwrap().freed.clone()
    }

    pub fn clear_freed(&self) {
        self.state.lock().unwrap().freed.clear();
    }

    fn active<R>(f: impl FnOnce(&Self) -> R) -> R {
        let active = ACTIVE_ARENA.lock().unwrap();
        let address = active.expect("no active paging test arena");
        drop(active);
        // SAFETY: each fixture retains its arena until all allocator calls finish.
        f(unsafe { &*(address as *const Self) })
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut active = ACTIVE_ARENA.lock().unwrap();
        assert_eq!(*active, Some(self as *const Self as usize));
        *active = None;
        ACTIVE_ARENA_CHANGED.notify_one();
    }
}

/// The arena as a direct map: identity, so a walk can follow it on the host.
#[derive(Clone, Copy)]
pub struct Allocator;

#[derive(Clone, Copy)]
pub struct RebasedAllocator;

unsafe impl DirectMappedAllocator for Allocator {
    fn share_count(paddr: PhysAddr) -> &'static AtomicUsize {
        share_counter(paddr)
    }

    fn direct_map() -> (core::ops::Range<PhysAddr>, VirtAddr) {
        Arena::active(|arena| {
            (
                PhysAddr::from(arena.base)..PhysAddr::from(arena.base + arena.len),
                VirtAddr::from(arena.base),
            )
        })
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        Arena::active(|arena| {
            let mut state = arena.state.lock().unwrap();
            if state.next + 4096 > arena.base + arena.len {
                return Err(PagingError::AllocFrame);
            }
            let page = state.next;
            state.next += 4096;
            assert!(state.live.insert(page));
            // SAFETY: this private arena page is poisoned to expose missing initialization.
            unsafe { core::ptr::write_bytes(page as *mut u8, 0xff, 4096) };
            Ok(PhysAddr::from(page))
        })
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        Arena::active(|arena| {
            let page = paddr.bits();
            assert_eq!(page % 4096, 0, "table page is not page-aligned");
            assert!(
                (arena.base..arena.base + arena.len).contains(&page),
                "table page is outside the arena"
            );
            let mut state = arena.state.lock().unwrap();
            assert!(page < state.next, "table page was not allocated by this arena");
            assert!(state.live.remove(&page), "table page is not currently live");
            state.freed.push(page);
        });
    }
}

/// One process-wide `AtomicUsize` per physical frame, leaked on first use so
/// [`DirectMappedAllocator::share_count`] can hand out a `&'static` reference.
static SHARE_COUNTS: Mutex<BTreeMap<usize, &'static AtomicUsize>> = Mutex::new(BTreeMap::new());

fn share_counter(paddr: PhysAddr) -> &'static AtomicUsize {
    *SHARE_COUNTS
        .lock()
        .unwrap()
        .entry(paddr.bits())
        .or_insert_with(|| Box::leak(Box::new(AtomicUsize::new(0))))
}

// SAFETY: the active arena provides one alignment-preserving address bijection.
unsafe impl DirectMappedAllocator for RebasedAllocator {
    fn direct_map() -> (Range<PhysAddr>, VirtAddr) {
        Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            (
                PhysAddr::from(physical)..PhysAddr::from(physical + arena.len()),
                VirtAddr::from(arena.base),
            )
        })
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        let page = Allocator::allocate_table_page()?;
        Ok(Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            PhysAddr::from(page.bits() - arena.base() + physical)
        }))
    }

    unsafe fn deallocate_table_page(page: PhysAddr) {
        assert_eq!(page.bits() % 4096, 0, "table page is not page-aligned");
        assert!(Self::direct_map().0.contains(&page), "table page is outside the direct map");
        let page = Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            PhysAddr::from(page.bits() - physical + arena.base())
        });
        // SAFETY: undoing the address bijection recovers the original allocated page.
        unsafe { Allocator::deallocate_table_page(page) };
    }
}

/// Four-level paging, the depth most of these tests care about.
pub type Table = KernelPageTable<X86_64Paging<Host>, Allocator, Lvl<3>>;

pub const ARENA: usize = 2 * 1024 * 1024;

/// An arena and a table built over it, mapping the arena and nothing else.
pub fn table() -> (Arc<Arena>, Table) {
    let arena = Arena::new(ARENA);
    let table = Table::new(PTEntryFlags::data()).unwrap();
    (arena, table)
}

pub fn flags() -> PTEntryFlags {
    PTEntryFlags::data()
}

/// The table pages the root points at.
pub fn root_children<S: PagingOwnershipPolicy>(
    table: &PageTable<X86_64Paging<Host>, Allocator, Lvl<3>, S>,
) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}

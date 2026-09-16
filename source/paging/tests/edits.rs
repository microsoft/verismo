//! Protection, splitting, and encryption updates over host-backed page tables.

mod common;

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::ops::Range;
#[cfg(feature = "concurrent")]
use std::ops::{Deref, DerefMut};
#[cfg(feature = "concurrent")]
use std::panic::resume_unwind;
use std::panic::{catch_unwind, AssertUnwindSafe};
#[cfg(feature = "concurrent")]
use std::sync::atomic::AtomicBool;
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(feature = "concurrent")]
use std::sync::{mpsc, Barrier, MutexGuard};
use std::sync::{Arc, Mutex};
#[cfg(feature = "concurrent")]
use std::thread::{self, JoinHandle};
#[cfg(feature = "concurrent")]
use std::time::Duration;

use common::{Allocator, Arena, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::{Lvl, PageLevel};
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::os_contract::{DirectMappedAllocator, PagingError};
#[cfg(feature = "concurrent")]
use paging::pagetable::LockSpec;
use paging::pagetable::PageTable;
use paging::sizes::entry_index;
use paging::tlb::MayNeedFlush;
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams, X86TlbFlushTok};

const PAGE: usize = 4096;
const LARGE: usize = 2 * 1024 * 1024;
const HUGE: usize = 1024 * 1024 * 1024;
const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x4_0000_0000;
const OTHER_FRAME: usize = 0x8_0000_0000;
const PRIVATE: usize = 1 << 51;
const SMALL_LEVEL: PageLevel = PageLevel::Level0;
const LARGE_LEVEL: PageLevel = PageLevel::Level1;
const HUGE_LEVEL: PageLevel = PageLevel::Level2;
#[cfg(feature = "concurrent")]
const WAIT: Duration = Duration::from_secs(10);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Tagged;

unsafe impl X86PagingParams for Tagged {
    fn private_mask() -> usize {
        PRIVATE
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(scope: FlushScope) {
        observe_flush(scope, true);
    }

    fn flush_tlb_global_percpu(scope: FlushScope) {
        observe_flush(scope, false);
    }

    fn flush_tlb_ignore_global_sync(_scope: FlushScope) {
        panic!("live splits must invalidate global translations");
    }

    fn flush_tlb_ignore_global_percpu(_scope: FlushScope) {
        panic!("live splits must invalidate global translations");
    }
}

type Arch = X86Paging<Tagged>;
type Entry = PTEntry<Arch>;
type Flush = MayNeedFlush<X86TlbFlushTok<Tagged>>;
#[cfg(not(feature = "concurrent"))]
type Table = PageTable<Arch, BudgetAllocator, Lvl<3>>;
#[cfg(feature = "concurrent")]
type Table = PageTable<Arch, BudgetAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(feature = "concurrent")]
type ResolutionCountingTable = PageTable<Arch, ResolutionCountingAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(feature = "concurrent")]
type TwoLevelTable = PageTable<Arch, BudgetAllocator, Lvl<1>, WholeTreeLock>;

#[derive(Clone, Copy)]
struct BbmArchitecture;

impl paging::ArchPagingMeta for BbmArchitecture {
    type PTFlags = PTEntryFlags;
    type TlbFlushTok = X86TlbFlushTok<Tagged>;

    fn private_pte_mask() -> usize {
        PRIVATE
    }

    fn shared_pte_mask() -> usize {
        0
    }

    fn address_mask() -> usize {
        0x000f_ffff_ffff_f000
    }

    fn accessed_dirty_mask() -> usize {
        (PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY).bits()
    }

    fn requires_break_before_make(old: usize, new: usize, _: PageLevel) -> bool {
        old & PTEntryFlags::PRESENT.bits() != 0
            && new & PTEntryFlags::PRESENT.bits() != 0
            && old & PTEntryFlags::HUGE.bits() != new & PTEntryFlags::HUGE.bits()
    }
}

#[cfg(not(feature = "concurrent"))]
type BbmTable = PageTable<BbmArchitecture, BudgetAllocator, Lvl<3>>;
#[cfg(feature = "concurrent")]
type BbmTable = PageTable<BbmArchitecture, BudgetAllocator, Lvl<3>, WholeTreeLock>;
type FlushHook = Box<dyn FnMut(FlushScope, bool)>;
#[cfg(feature = "concurrent")]
type DeallocationHook = Box<dyn FnMut(PhysAddr) + Send>;

thread_local! {
    static FLUSHES: RefCell<Vec<(FlushScope, bool)>> = const { RefCell::new(Vec::new()) };
    static FLUSH_HOOK: RefCell<Option<FlushHook>> = RefCell::new(None);
    #[cfg(feature = "concurrent")]
    static RESOLVED_PAGES: RefCell<Vec<PhysAddr>> = const { RefCell::new(Vec::new()) };
}

#[cfg(feature = "concurrent")]
fn take_resolved_pages() -> Vec<PhysAddr> {
    RESOLVED_PAGES.with(|pages| std::mem::take(&mut *pages.borrow_mut()))
}

#[cfg(feature = "concurrent")]
fn assert_resolved_once(pages: &[PhysAddr], page: PhysAddr) {
    assert_eq!(
        pages.iter().filter(|resolved| **resolved == page).count(),
        1,
        "{page:?}: {pages:?}"
    );
}

fn observe_flush(scope: FlushScope, all_cpus: bool) {
    FLUSHES.with(|flushes| flushes.borrow_mut().push((scope, all_cpus)));
    FLUSH_HOOK.with(|hook| {
        if let Some(hook) = hook.borrow_mut().as_mut() {
            hook(scope, all_cpus);
        }
    });
}

fn take_flushes() -> Vec<(FlushScope, bool)> {
    FLUSHES.with(|flushes| std::mem::take(&mut *flushes.borrow_mut()))
}

fn set_flush_hook(hook: impl FnMut(FlushScope, bool) + 'static) {
    FLUSH_HOOK.with(|current| {
        assert!(current.borrow_mut().replace(Box::new(hook)).is_none());
    });
}

fn clear_flush_hook() {
    FLUSH_HOOK.with(|hook| *hook.borrow_mut() = None);
}

struct BudgetAllocator;
static ALLOCATION_BUDGET: AtomicUsize = AtomicUsize::new(usize::MAX);
#[cfg(feature = "concurrent")]
static ALLOCATION_GATE: Mutex<Option<Gate>> = Mutex::new(None);
#[cfg(feature = "concurrent")]
static DEALLOCATION_HOOK: Mutex<Option<DeallocationHook>> = Mutex::new(None);

// SAFETY: the existing host allocator owns the direct map and all allocated
// pages; the budget and hooks only control allocation timing or observe reclamation.
unsafe impl DirectMappedAllocator for BudgetAllocator {
    fn direct_map() -> (Range<PhysAddr>, VirtAddr) {
        Allocator::direct_map()
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        ALLOCATION_BUDGET
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |left| left.checked_sub(1))
            .map_err(|_| PagingError::AllocFrame)?;
        let page = Allocator::allocate_table_page()?;
        #[cfg(feature = "concurrent")]
        {
            let gate = ALLOCATION_GATE.lock().unwrap().take();
            if let Some(gate) = gate {
                gate.entered.send(()).unwrap();
                gate.release.recv_timeout(WAIT).expect("paused allocation was not released");
            }
        }
        Ok(page)
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        #[cfg(feature = "concurrent")]
        if let Some(hook) = DEALLOCATION_HOOK.lock().unwrap().as_mut() {
            hook(paddr);
        }
        // SAFETY: the caller supplies an unlinked page from this allocator.
        unsafe { Allocator::deallocate_table_page(paddr) };
    }
}

#[cfg(feature = "concurrent")]
struct ResolutionCountingAllocator;

// SAFETY: recording resolutions does not alter the active allocator domain or addresses.
#[cfg(feature = "concurrent")]
unsafe impl paging::os_contract::PagingAllocator for ResolutionCountingAllocator {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
        RESOLVED_PAGES.with(|pages| pages.borrow_mut().push(paddr));
        <BudgetAllocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(paddr)
    }

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
        <BudgetAllocator as paging::os_contract::PagingAllocator>::vaddr_to_paddr(vaddr)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        <BudgetAllocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: the caller transfers an unlinked page from this unchanged allocator domain.
        unsafe { <BudgetAllocator as DirectMappedAllocator>::deallocate_table_page(paddr) };
    }
}

#[cfg(feature = "concurrent")]
struct Gate {
    entered: mpsc::Sender<()>,
    release: mpsc::Receiver<()>,
}

#[derive(Default)]
struct LockState {
    #[cfg(feature = "concurrent")]
    content: Mutex<()>,
    #[cfg(feature = "concurrent")]
    gate: Mutex<Option<Gate>>,
    #[cfg(feature = "concurrent")]
    attempts: Mutex<Option<mpsc::Sender<()>>>,
    page_calls: AtomicUsize,
    before_unlock: Mutex<Option<Box<dyn FnMut() + Send>>>,
}

#[derive(Clone, Default)]
struct WholeTreeLock(Arc<LockState>);

impl WholeTreeLock {
    #[cfg(feature = "concurrent")]
    fn pause_next(&self) -> (mpsc::Receiver<()>, mpsc::Sender<()>) {
        let (entered, observed) = mpsc::channel();
        let (release, resumed) = mpsc::channel();
        assert!(self.0.gate.lock().unwrap().replace(Gate { entered, release: resumed }).is_none());
        (observed, release)
    }

    #[cfg(feature = "concurrent")]
    fn acquire(&self) -> WholeTreeGuard<'_> {
        let gate = self.0.gate.lock().unwrap().take();
        if let Some(gate) = gate {
            gate.entered.send(()).unwrap();
            gate.release.recv_timeout(WAIT).expect("paused lock was not released");
        }
        if let Some(attempts) = self.0.attempts.lock().unwrap().as_ref() {
            let _ = attempts.send(());
        }
        let inner = self.0.content.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        WholeTreeGuard { inner, state: &self.0 }
    }
}

#[cfg(feature = "concurrent")]
struct WholeTreeGuard<'a> {
    inner: MutexGuard<'a, ()>,
    state: &'a LockState,
}

#[cfg(feature = "concurrent")]
impl Deref for WholeTreeGuard<'_> {
    type Target = ();

    fn deref(&self) -> &() {
        &self.inner
    }
}

#[cfg(feature = "concurrent")]
impl DerefMut for WholeTreeGuard<'_> {
    fn deref_mut(&mut self) -> &mut () {
        &mut self.inner
    }
}

#[cfg(feature = "concurrent")]
impl Drop for WholeTreeGuard<'_> {
    fn drop(&mut self) {
        if let Some(hook) = self.state.before_unlock.lock().unwrap().as_mut() {
            hook();
        }
    }
}

// SAFETY: every physical key uses the same stable mutex. Its borrowed guard
// provides exclusion and releases the lock through the standard RAII path.
#[cfg(feature = "concurrent")]
unsafe impl LockSpec<()> for WholeTreeLock {
    type Guard<'a> = WholeTreeGuard<'a>;

    fn lock(&self, _page: PhysAddr) -> Self::Guard<'_> {
        self.0.page_calls.fetch_add(1, Ordering::SeqCst);
        self.acquire()
    }
}

struct Fixture {
    arena: Arc<Arena>,
    locks: WholeTreeLock,
}

impl Fixture {
    fn new() -> Self {
        take_flushes();
        clear_flush_hook();
        let arena = Arena::new(ARENA);
        ALLOCATION_BUDGET.store(usize::MAX, Ordering::SeqCst);
        Self { arena, locks: WholeTreeLock::default() }
    }

    fn allow_allocations(&self, count: usize) {
        ALLOCATION_BUDGET.store(count, Ordering::SeqCst);
    }

    #[cfg(feature = "concurrent")]
    fn pause_next_allocation(&self) -> (mpsc::Receiver<()>, mpsc::Sender<()>) {
        let (entered, observed) = mpsc::channel();
        let (release, resumed) = mpsc::channel();
        assert!(ALLOCATION_GATE
            .lock()
            .unwrap()
            .replace(Gate { entered, release: resumed })
            .is_none());
        (observed, release)
    }

    fn assert_all_reclaimed(&self) {
        let freed = self.arena.freed();
        assert_eq!(freed.len(), self.arena.allocated());
        assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), freed.len());
    }

    #[cfg(feature = "concurrent")]
    fn check_deallocation_is_unlocked(&self) {
        let locks = self.locks.clone();
        *DEALLOCATION_HOOK.lock().unwrap() = Some(Box::new(move |_| {
            assert!(locks.0.content.try_lock().is_ok(), "staging was reclaimed under content lock");
        }));
    }
}

fn fixture() -> (Fixture, Table) {
    let fixture = Fixture::new();
    #[cfg(not(feature = "concurrent"))]
    let table = Table::new(PTEntryFlags::data()).unwrap();
    #[cfg(feature = "concurrent")]
    let table = Table::new(fixture.locks.clone(), PTEntryFlags::data()).unwrap();
    (fixture, table)
}

fn bbm_fixture() -> (Fixture, BbmTable) {
    let fixture = Fixture::new();
    #[cfg(not(feature = "concurrent"))]
    let table = BbmTable::new(PTEntryFlags::data()).unwrap();
    #[cfg(feature = "concurrent")]
    let table = BbmTable::new(fixture.locks.clone(), PTEntryFlags::data()).unwrap();
    (fixture, table)
}

#[cfg(feature = "concurrent")]
fn resolution_counting_fixture() -> (Fixture, ResolutionCountingTable) {
    let (fixture, original) = fixture();
    let (locks, root) = original.leak();
    // SAFETY: leak transfers the inactive tree; the wrapper preserves its allocator and lock domains.
    let table = unsafe { ResolutionCountingTable::from_root(locks, root) }.unwrap();
    take_resolved_pages();
    (fixture, table)
}

fn discharge(flush: Flush) {
    // SAFETY: these test trees are never installed in hardware.
    unsafe { flush.ignore() };
}

fn assert_flush_covers(flush: Flush, start: usize, end: usize) {
    assert!(take_flushes().is_empty(), "a deferred edit flushed synchronously");
    assert_pending_covers(flush, start, end);
}

fn assert_pending_covers(flush: Flush, start: usize, end: usize) {
    match flush.scope().as_ref().expect("changed mapping must require a flush").scope() {
        FlushScope::All => {}
        FlushScope::Range { start: actual_start, end: actual_end, .. } => {
            assert!(actual_start.bits() <= start);
            assert!(actual_end.bits() >= end);
        }
    }
    discharge(flush);
}

fn assert_completed(flush: Flush, start: usize, end: usize, level: PageLevel) {
    flush.expect_no_flush();
    assert_eq!(
        take_flushes(),
        vec![(FlushScope::Range { start: start.into(), end: end.into(), level }, true)]
    );
}

fn old_flags() -> PTEntryFlags {
    PTEntryFlags::PRESENT
        | PTEntryFlags::NX
        | PTEntryFlags::GLOBAL
        | PTEntryFlags::NO_CACHE
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY
}

fn new_flags() -> PTEntryFlags {
    PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::USER
        | PTEntryFlags::WRITE_THROUGH
}

fn pat_bit(level: PageLevel) -> usize {
    1 << if level == SMALL_LEVEL { 7 } else { 12 }
}

fn leaf_word(
    frame: usize,
    level: PageLevel,
    flags: PTEntryFlags,
    shared: bool,
    pat: bool,
) -> usize {
    common::published_bits(
        frame
            | if shared { 0 } else { PRIVATE }
            | (flags & !PTEntryFlags::HUGE).bits()
            | if level == SMALL_LEVEL { 0 } else { PTEntryFlags::HUGE.bits() }
            | if pat { pat_bit(level) } else { 0 },
    )
}

fn protected_word(old: usize, flags: PTEntryFlags) -> usize {
    let replaced = (PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::USER
        | PTEntryFlags::WRITE_THROUGH
        | PTEntryFlags::NO_CACHE
        | PTEntryFlags::GLOBAL
        | PTEntryFlags::NX)
        .bits();
    (old & !replaced) | (flags.bits() & replaced)
}

unsafe fn leaf_slot(root: PhysAddr, address: VirtAddr) -> (*mut Entry, PageLevel) {
    let mut page = root.bits();
    let mut level = PageLevel::Level3;
    loop {
        let slot = (page as *mut Entry).wrapping_add(entry_index(address, level));
        // SAFETY: the caller owns this live host-backed tree; table addresses
        // are identity-mapped, and no references into PTE storage are created.
        let entry = unsafe { Entry::load_entry(slot) };
        if !entry.is_table(level) {
            return (slot, level);
        }
        page = entry.address();
        level = level.child().unwrap();
    }
}

unsafe fn seed_pat(root: PhysAddr, address: VirtAddr) {
    // SAFETY: the caller exclusively owns the tree during this fixture edit.
    let (slot, level) = unsafe { leaf_slot(root, address) };
    let entry = unsafe { Entry::load_entry(slot) };
    assert!(entry.is_leaf(level));
    unsafe { Entry::store_entry(slot, Entry::from_bits(entry.raw() | pat_bit(level))) };
}

unsafe fn assert_permissive_ancestors(root: PhysAddr, address: VirtAddr) {
    let mut page = root.bits();
    let mut level = PageLevel::Level3;
    loop {
        let slot = (page as *const Entry).wrapping_add(entry_index(address, level));
        // SAFETY: the caller pins the tree, and all accesses use atomic loads.
        let entry = unsafe { Entry::load_entry(slot) };
        if !entry.is_table(level) {
            assert!(entry.is_leaf(level));
            return;
        }
        assert!(entry.writable(), "ancestor at {level:?} blocks write permission");
        assert!(entry.user(), "ancestor at {level:?} blocks user permission");
        assert!(
            !entry.flags().contains(PTEntryFlags::NX),
            "ancestor at {level:?} blocks execution"
        );
        page = entry.address();
        level = level.child().unwrap();
    }
}

#[test]
fn architecture_policy_can_require_break_before_make_for_a_split() {
    type BbmEntry = PTEntry<BbmArchitecture>;

    let (fixture, mut table) = bbm_fixture();
    let base = VirtAddr::from(BASE);
    table.map(base, FRAME.into(), HUGE_LEVEL, old_flags(), false).unwrap();
    let (slot, level) = unsafe { leaf_slot(table.root_paddr(), base) };
    assert_eq!(level, HUGE_LEVEL);
    let old = table.walk(base).read().raw();
    let slot = slot as usize;
    set_flush_hook(move |_, _| {
        let entry = unsafe { BbmEntry::load_entry(slot as *const BbmEntry) };
        assert_eq!(entry.raw(), old & !PTEntryFlags::PRESENT.bits());
    });
    table.split(base + PAGE, SMALL_LEVEL, true).unwrap().expect_no_flush();
    clear_flush_hook();
    assert_eq!(table.walk(base + PAGE).level(), SMALL_LEVEL);
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[test]
fn architecture_bbm_range_breaks_only_structural_boundaries() {
    type BbmEntry = PTEntry<BbmArchitecture>;

    let (fixture, mut table) = bbm_fixture();
    let base = VirtAddr::from(BASE);
    let mut slots = Vec::new();
    for index in 0..3 {
        let address = base + index * HUGE;
        table.map(address, (FRAME + index * HUGE).into(), HUGE_LEVEL, old_flags(), false).unwrap();
        slots.push(unsafe { leaf_slot(table.root_paddr(), address).0 as usize });
    }
    set_flush_hook(move |_, _| {
        let mut invalid = 0;
        for (index, slot) in slots.iter().copied().enumerate() {
            let entry = unsafe { BbmEntry::load_entry(slot as *const BbmEntry) };
            if index == 1 {
                assert!(entry.is_leaf(HUGE_LEVEL));
                if !cfg!(feature = "concurrent") {
                    assert!(entry.writable());
                }
            } else if entry.present() {
                assert!(entry.is_leaf(HUGE_LEVEL) || entry.is_table(HUGE_LEVEL));
            } else {
                invalid += 1;
            }
        }
        if cfg!(feature = "concurrent") {
            assert!(invalid <= 1);
        } else {
            assert_eq!(invalid, 2);
        }
    });
    let (result, flush) =
        table.mprotect_range(base + PAGE, base + 3 * HUGE - PAGE, new_flags(), true);
    result.unwrap();
    if cfg!(feature = "concurrent") {
        discharge(flush);
        assert_eq!(take_flushes().len(), 2);
    } else {
        assert_completed(flush, BASE, BASE + 3 * HUGE, HUGE_LEVEL);
    }
    clear_flush_hook();
    assert_eq!(table.walk(base + PAGE).level(), SMALL_LEVEL);
    assert_eq!(table.walk(base + HUGE).level(), HUGE_LEVEL);
    assert_eq!(table.walk(base + 3 * HUGE - PAGE).level(), SMALL_LEVEL);
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn two_level_range_can_split_both_boundaries_before_updating() {
    let fixture = Fixture::new();
    let mut table = TwoLevelTable::new(fixture.locks.clone(), PTEntryFlags::data()).unwrap();
    let base = VirtAddr::from(BASE);
    for index in 0..3 {
        table
            .map(
                base + index * LARGE,
                PhysAddr::from(FRAME + index * LARGE),
                LARGE_LEVEL,
                old_flags(),
                false,
            )
            .unwrap();
    }

    let start = base + PAGE;
    let end = base + 3 * LARGE - PAGE;
    let (result, flush) = table.mprotect_range(start, end, new_flags(), true);

    assert_eq!(result, Ok(()));
    discharge(flush);
    assert!(!table.walk(base).read().writable());
    assert_eq!(table.walk(start).level(), SMALL_LEVEL);
    assert!(table.walk(start).read().writable());
    assert!(table.walk(end - PAGE).read().writable());
    assert!(!table.walk(end).read().writable());
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

macro_rules! edit_tests {
    ($module:ident, $fixture:ident) => {
        mod $module {
            #![allow(unused_mut)]

            use super::*;

            #[test]
            fn same_size_protection_replaces_permissions_but_preserves_frame_tags_pat_and_ad() {
                let (fixture, mut table) = $fixture();
                for (index, level) in [SMALL_LEVEL, LARGE_LEVEL, HUGE_LEVEL].into_iter().enumerate()
                {
                    for shared in [false, true] {
                        let address =
                            VirtAddr::from(BASE + (index * 2 + usize::from(shared)) * HUGE);
                        table
                            .map(address, PhysAddr::from(FRAME), level, old_flags(), shared)
                            .unwrap();
                        // SAFETY: no other thread or hardware can access this fixture.
                        unsafe { seed_pat(table.root_paddr(), address) };
                        let original = table.walk(address).read().raw();
                        assert_eq!(original, leaf_word(FRAME, level, old_flags(), shared, true));
                        let allocated = fixture.arena.allocated();
                        fixture.allow_allocations(0);

                        for requested in [
                            new_flags(),
                            PTEntryFlags::PRESENT,
                            PTEntryFlags::PRESENT | PTEntryFlags::NO_CACHE | PTEntryFlags::NX,
                        ] {
                            let flush = table.mprotect(address, level, requested, true).unwrap();
                            assert_flush_covers(
                                flush,
                                address.bits(),
                                address.bits() + level.size(),
                            );
                            assert_eq!(
                                table.walk(address).read().raw(),
                                protected_word(original, requested)
                            );
                            assert_eq!(table.walk(address).level(), level);
                            for offset in [0, level.size() - 1] {
                                assert_eq!(
                                    table.phys_addr(address + offset),
                                    Ok(PhysAddr::from(FRAME + offset))
                                );
                            }
                        }
                        assert_eq!(fixture.arena.allocated(), allocated);
                        fixture.allow_allocations(usize::MAX);
                    }
                }
                assert_eq!(table.validate_page_table(), Ok(()));
            }

            #[test]
            fn protecting_a_subpage_of_a_huge_leaf_changes_only_that_page() {
                let (fixture, mut table) = $fixture();
                for (index, level) in [LARGE_LEVEL, HUGE_LEVEL].into_iter().enumerate() {
                    let base = BASE + index * HUGE;
                    let target_offset =
                        if level == HUGE_LEVEL { LARGE + 7 * PAGE } else { 7 * PAGE };
                    let target = VirtAddr::from(base + target_offset);
                    table
                        .map(VirtAddr::from(base), PhysAddr::from(FRAME), level, old_flags(), false)
                        .unwrap();
                    // SAFETY: the fixture has no concurrent users.
                    unsafe { seed_pat(table.root_paddr(), target) };
                    let allocated = fixture.arena.allocated();
                    let flush = table.mprotect(target, SMALL_LEVEL, new_flags(), true).unwrap();
                    assert_completed(flush, base, base + level.size(), level);
                    assert_eq!(fixture.arena.allocated() - allocated, level.depth());

                    let small_base = target_offset & !(LARGE - 1);
                    for page in 0..512 {
                        let offset = small_base + page * PAGE;
                        let address = VirtAddr::from(base + offset);
                        let old = leaf_word(FRAME + offset, SMALL_LEVEL, old_flags(), false, true);
                        let expected = if offset == target_offset {
                            protected_word(old, new_flags())
                        } else {
                            old
                        };
                        assert_eq!(table.walk(address).level(), SMALL_LEVEL);
                        assert_eq!(
                            table.walk(address).read().raw(),
                            expected,
                            "offset {offset:#x}"
                        );
                        assert_eq!(
                            table.phys_addr(address + PAGE - 1),
                            Ok(PhysAddr::from(FRAME + offset + PAGE - 1))
                        );
                    }
                    if level == HUGE_LEVEL {
                        for page in 0..512 {
                            let offset = page * LARGE;
                            if offset == small_base {
                                continue;
                            }
                            let address = VirtAddr::from(base + offset);
                            assert_eq!(table.walk(address).level(), LARGE_LEVEL);
                            assert_eq!(
                                table.walk(address).read().raw(),
                                leaf_word(FRAME + offset, LARGE_LEVEL, old_flags(), false, true)
                            );
                            assert_eq!(
                                table.phys_addr(address + LARGE - 1),
                                Ok(PhysAddr::from(FRAME + offset + LARGE - 1))
                            );
                        }
                    }
                    // SAFETY: the tree is live and no other thread accesses it.
                    unsafe { assert_permissive_ancestors(table.root_paddr(), target) };
                }
                assert_eq!(table.validate_page_table(), Ok(()));
            }

            #[test]
            fn range_protection_handles_small_heads_and_tails_around_a_one_gib_leaf() {
                let (fixture, mut table) = $fixture();
                let head = BASE + HUGE - LARGE;
                let middle = BASE + HUGE;
                let tail = BASE + 2 * HUGE;
                for (address, frame, level) in [
                    (head, FRAME, LARGE_LEVEL),
                    (middle, FRAME + HUGE, HUGE_LEVEL),
                    (tail, FRAME + 2 * HUGE, LARGE_LEVEL),
                ] {
                    table
                        .map(
                            VirtAddr::from(address),
                            PhysAddr::from(frame),
                            level,
                            old_flags(),
                            false,
                        )
                        .unwrap();
                }
                let allocated = fixture.arena.allocated();
                let start = middle - PAGE;
                let end = tail + PAGE;
                let originals: Vec<_> = [head, middle, tail]
                    .into_iter()
                    .map(|address| {
                        let (slot, level) =
                            unsafe { leaf_slot(table.root_paddr(), address.into()) };
                        assert_eq!(level, if address == middle { HUGE_LEVEL } else { LARGE_LEVEL });
                        (slot as usize, table.walk(address.into()).read().raw())
                    })
                    .collect();
                assert_ne!(originals[0].0 / PAGE, originals[2].0 / PAGE);
                set_flush_hook(move |scope, all_cpus| {
                    assert!(all_cpus);
                    if cfg!(feature = "concurrent") {
                        assert!(matches!(
                            scope,
                            FlushScope::Range { start, end, level: LARGE_LEVEL }
                                if (start == head.into() && end == middle.into())
                                    || (start == tail.into() && end == (tail + LARGE).into())
                        ));
                    } else {
                        assert_eq!(
                            scope,
                            FlushScope::Range {
                                start: head.into(),
                                end: (tail + LARGE).into(),
                                level: LARGE_LEVEL,
                            }
                        );
                    }
                    for (index, (slot, _)) in originals.iter().enumerate() {
                        let entry = unsafe { Entry::load_entry(*slot as *const Entry) };
                        if index == 1 {
                            assert!(entry.is_leaf(HUGE_LEVEL));
                        } else {
                            assert!(
                                entry.is_leaf(LARGE_LEVEL) || entry.is_table(LARGE_LEVEL)
                            );
                        }
                    }
                });
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(start),
                    VirtAddr::from(end),
                    new_flags(),
                    true,
                );
                clear_flush_hook();
                assert_eq!(result, Ok(()));
                if cfg!(feature = "concurrent") {
                    discharge(flush);
                    assert_eq!(take_flushes().len(), 2);
                } else {
                    assert_completed(flush, head, tail + LARGE, LARGE_LEVEL);
                }
                assert_eq!(fixture.arena.allocated() - allocated, 2);
                assert_eq!(table.walk(VirtAddr::from(middle)).level(), HUGE_LEVEL);
                assert_eq!(
                    table.walk(VirtAddr::from(middle)).read().raw(),
                    protected_word(
                        leaf_word(FRAME + HUGE, HUGE_LEVEL, old_flags(), false, false),
                        new_flags()
                    )
                );
                for page in 0..512 {
                    for (base, frame, protected_page) in
                        [(head, FRAME, 511), (tail, FRAME + 2 * HUGE, 0)]
                    {
                        let offset = page * PAGE;
                        let address = VirtAddr::from(base + offset);
                        let old = leaf_word(frame + offset, SMALL_LEVEL, old_flags(), false, false);
                        let expected = if page == protected_page {
                            protected_word(old, new_flags())
                        } else {
                            old
                        };
                        assert_eq!(table.walk(address).read().raw(), expected);
                        assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(frame + offset)));
                    }
                }
                assert_eq!(table.validate_page_table(), Ok(()));
            }

            #[test]
            fn range_protection_keeps_existing_large_and_small_leaf_sizes_without_allocating() {
                let (fixture, mut table) = $fixture();
                let start = BASE + LARGE - PAGE;
                let end = BASE + 2 * LARGE + PAGE;
                for (address, level) in [
                    (start, SMALL_LEVEL),
                    (BASE + LARGE, LARGE_LEVEL),
                    (BASE + 2 * LARGE, SMALL_LEVEL),
                ] {
                    table
                        .map(
                            VirtAddr::from(address),
                            PhysAddr::from(FRAME),
                            level,
                            old_flags(),
                            true,
                        )
                        .unwrap();
                }
                let allocated = fixture.arena.allocated();
                fixture.allow_allocations(0);
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(start),
                    VirtAddr::from(end),
                    new_flags(),
                    true,
                );
                assert_eq!(result, Ok(()));
                assert_flush_covers(flush, start, end);
                assert_eq!(fixture.arena.allocated(), allocated);
                for (address, level) in [
                    (start, SMALL_LEVEL),
                    (BASE + LARGE, LARGE_LEVEL),
                    (BASE + 2 * LARGE, SMALL_LEVEL),
                ] {
                    assert_eq!(table.walk(VirtAddr::from(address)).level(), level);
                    assert_eq!(
                        table.walk(VirtAddr::from(address)).read().raw(),
                        protected_word(
                            leaf_word(FRAME, level, old_flags(), true, false),
                            new_flags()
                        )
                    );
                }
            }

            #[test]
            fn a_range_stops_at_a_hole_and_returns_the_successful_prefix_flush() {
                let (_fixture, mut table) = $fixture();
                for page in [0, 1, 3] {
                    table
                        .map_4k(
                            VirtAddr::from(BASE + page * PAGE),
                            PhysAddr::from(FRAME + page * PAGE),
                            old_flags(),
                            false,
                        )
                        .unwrap();
                }
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(BASE),
                    VirtAddr::from(BASE + 4 * PAGE),
                    new_flags(),
                    true,
                );
                assert_eq!(result, Err(PagingError::NotMapped));
                assert_flush_covers(flush, BASE, BASE + 2 * PAGE);
                for page in [0, 1, 3] {
                    let old =
                        leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, false);
                    let expected = if page < 2 { protected_word(old, new_flags()) } else { old };
                    assert_eq!(
                        table.walk(VirtAddr::from(BASE + page * PAGE)).read().raw(),
                        expected
                    );
                }
                assert_eq!(
                    table.phys_addr(VirtAddr::from(BASE + 2 * PAGE)),
                    Err(PagingError::NotMapped)
                );
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(BASE + 2 * PAGE),
                    VirtAddr::from(BASE + 4 * PAGE),
                    new_flags(),
                    true,
                );
                assert_eq!(result, Err(PagingError::NotMapped));
                flush.expect_no_flush();
                assert_eq!(
                    table.walk(VirtAddr::from(BASE + 3 * PAGE)).read().raw(),
                    leaf_word(FRAME + 3 * PAGE, SMALL_LEVEL, old_flags(), false, false)
                );
            }

            #[test]
            fn empty_and_invalid_ranges_do_not_change_the_tree() {
                let (fixture, mut table) = $fixture();
                let address = VirtAddr::from(BASE);
                table.map_4k(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
                let original = table.walk(address).read().raw();
                let allocated = fixture.arena.allocated();
                fixture.allow_allocations(0);
                for empty in [address, VirtAddr::from(BASE + HUGE)] {
                    let (result, flush) = table.mprotect_range(empty, empty, new_flags(), true);
                    assert_eq!(result, Ok(()));
                    flush.expect_no_flush();
                }
                for (start, end) in [
                    (BASE + PAGE, BASE),
                    (BASE + 1, BASE + PAGE),
                    (BASE, BASE + PAGE - 1),
                    (BASE + 1, BASE + 1),
                ] {
                    let (result, flush) = table.mprotect_range(
                        VirtAddr::from(start),
                        VirtAddr::from(end),
                        new_flags(),
                        true,
                    );
                    assert_eq!(result, Err(PagingError::InvalidRange));
                    flush.expect_no_flush();
                }
                let (result, flush) =
                    table.mprotect_range(address, address + PAGE, PTEntryFlags::WRITABLE, true);
                assert_eq!(result, Err(PagingError::InvalidFlags));
                flush.expect_no_flush();
                assert_eq!(table.walk(address).read().raw(), original);
                assert_eq!(fixture.arena.allocated(), allocated);
            }

            #[test]
            fn failed_private_splits_leave_the_original_leaf_unchanged_and_reclaim_staging() {
                let (fixture, mut table) = $fixture();
                for operation in 0..4 {
                    for allowed in [0, 1] {
                        fixture.allow_allocations(usize::MAX);
                        let base = BASE + (operation * 2 + allowed) * HUGE;
                        let address = VirtAddr::from(base + 7 * PAGE);
                        table
                            .map(
                                VirtAddr::from(base),
                                PhysAddr::from(FRAME),
                                HUGE_LEVEL,
                                old_flags(),
                                false,
                            )
                            .unwrap();
                        // SAFETY: the test owns the tree without concurrent users.
                        unsafe { seed_pat(table.root_paddr(), address) };
                        let original = table.walk(address).read().raw();
                        let allocated = fixture.arena.allocated();
                        let freed = fixture.arena.freed().len();
                        fixture.allow_allocations(allowed);
                        let result = match operation {
                            0 => table.split(address, SMALL_LEVEL, true).map(discharge),
                            1 => table
                                .mprotect(address, SMALL_LEVEL, new_flags(), true)
                                .map(discharge),
                            2 => table.set_shared_4k(address, true).map(discharge),
                            _ => table.set_encrypted_4k(address, true).map(discharge),
                        };
                        assert_eq!(result, Err(PagingError::AllocFrame));
                        assert_eq!(table.walk(address).level(), HUGE_LEVEL);
                        assert_eq!(table.walk(address).read().raw(), original);
                        assert_eq!(fixture.arena.allocated() - allocated, allowed);
                        assert_eq!(fixture.arena.freed().len() - freed, allowed);
                        assert!(take_flushes().is_empty());
                        for offset in [0, 7 * PAGE, LARGE, HUGE - 1] {
                            assert_eq!(
                                table.phys_addr(VirtAddr::from(base + offset)),
                                Ok(PhysAddr::from(FRAME + offset))
                            );
                        }
                    }
                }
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: there are no software or hardware walkers, or shared subtrees.
                unsafe { table.free_children() };
                drop(table);
                fixture.assert_all_reclaimed();
            }

            #[test]
            fn range_allocation_failure_retains_only_completed_prefix_edits_and_their_flush() {
                let (fixture, mut table) = $fixture();
                for offset in [0, HUGE] {
                    table
                        .map(
                            VirtAddr::from(BASE + offset),
                            PhysAddr::from(FRAME + offset),
                            HUGE_LEVEL,
                            old_flags(),
                            false,
                        )
                        .unwrap();
                }
                let start = BASE + HUGE - PAGE;
                let end = BASE + HUGE + PAGE;
                fixture.allow_allocations(1);
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(start),
                    VirtAddr::from(end),
                    new_flags(),
                    true,
                );
                assert_eq!(result, Err(PagingError::AllocFrame));
                flush.expect_no_flush();
                for offset in [0, HUGE] {
                    assert_eq!(table.walk(VirtAddr::from(BASE + offset)).level(), HUGE_LEVEL);
                    assert_eq!(
                        table.walk(VirtAddr::from(BASE + offset)).read().raw(),
                        leaf_word(FRAME + offset, HUGE_LEVEL, old_flags(), false, false)
                    );
                }

                fixture.allow_allocations(2);
                let (result, flush) = table.mprotect_range(
                    VirtAddr::from(start),
                    VirtAddr::from(end),
                    new_flags(),
                    true,
                );
                assert_eq!(result, Err(PagingError::AllocFrame));
                assert_completed(flush, BASE, BASE + HUGE, HUGE_LEVEL);
                assert_eq!(
                    table.walk(VirtAddr::from(start)).read().raw(),
                    protected_word(
                        leaf_word(FRAME + HUGE - PAGE, SMALL_LEVEL, old_flags(), false, false),
                        new_flags()
                    )
                );
                assert_eq!(
                    table.walk(VirtAddr::from(start - PAGE)).read().raw(),
                    leaf_word(FRAME + HUGE - 2 * PAGE, SMALL_LEVEL, old_flags(), false, false)
                );
                assert_eq!(table.walk(VirtAddr::from(BASE + HUGE)).level(), HUGE_LEVEL);
                assert_eq!(
                    table.walk(VirtAddr::from(BASE + HUGE)).read().raw(),
                    leaf_word(FRAME + HUGE, HUGE_LEVEL, old_flags(), false, false)
                );
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: the test has exclusive access and never installs its tree.
                unsafe { table.free_children() };
                drop(table);
                fixture.assert_all_reclaimed();
            }

            #[test]
            fn split_is_idempotent_preserves_every_mapping_and_remains_reclaimable() {
                let (fixture, mut table) = $fixture();
                let start = VirtAddr::from(BASE);
                let target = start + LARGE + 7 * PAGE;
                assert!(matches!(
                    table.split(target, SMALL_LEVEL, true),
                    Err(PagingError::NotMapped)
                ));
                let allocated = fixture.arena.allocated();
                table.map(start, PhysAddr::from(FRAME), HUGE_LEVEL, old_flags(), false).unwrap();
                // SAFETY: this fixture has no other users.
                unsafe { seed_pat(table.root_paddr(), start) };
                let flush = table.split(target, SMALL_LEVEL, true).unwrap();
                assert_completed(flush, BASE, BASE + HUGE, HUGE_LEVEL);
                table.split(target, SMALL_LEVEL, true).unwrap().expect_no_flush();
                table.split(start, HUGE_LEVEL, true).unwrap().expect_no_flush();
                for large in 0..512 {
                    if large == 1 {
                        for small in 0..512 {
                            let offset = LARGE + small * PAGE;
                            let address = start + offset;
                            assert_eq!(table.walk(address).level(), SMALL_LEVEL);
                            assert_eq!(
                                table.walk(address).read().raw(),
                                leaf_word(FRAME + offset, SMALL_LEVEL, old_flags(), false, true)
                            );
                            assert_eq!(
                                table.phys_addr(address + PAGE - 1),
                                Ok(PhysAddr::from(FRAME + offset + PAGE - 1))
                            );
                        }
                    } else {
                        let offset = large * LARGE;
                        let address = start + offset;
                        assert_eq!(table.walk(address).level(), LARGE_LEVEL);
                        assert_eq!(
                            table.walk(address).read().raw(),
                            leaf_word(FRAME + offset, LARGE_LEVEL, old_flags(), false, true)
                        );
                        assert_eq!(
                            table.phys_addr(address + LARGE - 1),
                            Ok(PhysAddr::from(FRAME + offset + LARGE - 1))
                        );
                    }
                }
                let built = fixture.arena.allocated() - allocated;
                let (mapped, flush) = table.unmap_region(start, start + HUGE).unwrap();
                assert!(mapped);
                assert_flush_covers(flush, BASE, BASE + HUGE);
                // SAFETY: the unmapped range has no walkers or outstanding host TLB state.
                unsafe { table.free_page_table_by_range(start, start + HUGE) };
                assert_eq!(fixture.arena.freed().len(), built);
                assert_eq!(table.phys_addr(target), Err(PagingError::NotMapped));
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: all remaining subtrees belong exclusively to this inactive tree.
                unsafe { table.free_children() };
                drop(table);
                fixture.assert_all_reclaimed();
            }

            #[test]
            fn protection_refuses_finer_subtrees_and_leaf_edits_refuse_holes_without_changes() {
                let (fixture, mut table) = $fixture();
                let address = VirtAddr::from(BASE);
                for page in [0, 1, 511] {
                    table
                        .map_4k(
                            address + page * PAGE,
                            PhysAddr::from(FRAME + page * PAGE),
                            old_flags(),
                            false,
                        )
                        .unwrap();
                }
                let allocated = fixture.arena.allocated();
                fixture.allow_allocations(0);
                assert!(matches!(
                    table.mprotect(address, LARGE_LEVEL, new_flags(), true),
                    Err(PagingError::NotLeafEntry)
                ));
                for missing in [address + 2 * PAGE, address + HUGE] {
                    assert!(matches!(
                        table.mprotect(missing, SMALL_LEVEL, new_flags(), true),
                        Err(PagingError::NotMapped)
                    ));
                    assert!(matches!(
                        table.split(missing, SMALL_LEVEL, true),
                        Err(PagingError::NotMapped)
                    ));
                    assert!(matches!(
                        table.set_shared_4k(missing, true),
                        Err(PagingError::NotMapped)
                    ));
                    assert!(matches!(
                        table.set_encrypted_4k(missing, true),
                        Err(PagingError::NotMapped)
                    ));
                    assert_eq!(table.phys_addr(missing), Err(PagingError::NotMapped));
                }
                for page in [0, 1, 511] {
                    assert_eq!(
                        table.walk(address + page * PAGE).read().raw(),
                        leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, false)
                    );
                }
                assert_eq!(fixture.arena.allocated(), allocated);
                assert!(fixture.arena.freed().is_empty());
                assert_eq!(table.validate_page_table(), Ok(()));
            }

            #[test]
            fn invalid_leaf_edit_arguments_are_rejected_before_allocation_or_mutation() {
                let (fixture, mut table) = $fixture();
                let address = VirtAddr::from(BASE);
                table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
                let original = table.walk(address).read().raw();
                let allocated = fixture.arena.allocated();
                fixture.allow_allocations(0);
                for flags in [PTEntryFlags::empty(), PTEntryFlags::WRITABLE | PTEntryFlags::NX] {
                    assert!(matches!(
                        table.mprotect(address, SMALL_LEVEL, flags, true),
                        Err(PagingError::InvalidFlags)
                    ));
                }
                for (offset, level) in [(1, SMALL_LEVEL), (PAGE, LARGE_LEVEL)] {
                    assert!(matches!(
                        table.mprotect(address + offset, level, new_flags(), true),
                        Err(PagingError::InvalidAddress)
                    ));
                }
                let zero = VirtAddr::from(0usize);
                let invalid = PageLevel::Level4;
                assert!(matches!(table.split(zero, invalid, true), Err(PagingError::InvalidLevel)));
                assert!(matches!(
                    table.mprotect(zero, invalid, new_flags(), true),
                    Err(PagingError::InvalidLevel)
                ));
                assert_eq!(table.walk(address).read().raw(), original);
                assert_eq!(table.walk(address).level(), LARGE_LEVEL);
                assert_eq!(fixture.arena.allocated(), allocated);
                assert!(fixture.arena.freed().is_empty());
            }
        }
    };
}

edit_tests!(selected_controller, fixture);

#[cfg(feature = "concurrent")]
type Worker<T> = (JoinHandle<()>, mpsc::Receiver<thread::Result<T>>);

#[cfg(feature = "concurrent")]
fn spawn<T: Send + 'static>(job: impl FnOnce() -> T + Send + 'static) -> Worker<T> {
    let (send, receive) = mpsc::channel();
    let handle = thread::spawn(move || {
        let result = catch_unwind(AssertUnwindSafe(job));
        let _ = send.send(result);
    });
    (handle, receive)
}

#[cfg(feature = "concurrent")]
fn finish<T>((handle, receive): Worker<T>) -> T {
    let result = receive.recv_timeout(WAIT).expect("worker exceeded the deadline");
    handle.join().unwrap();
    result.unwrap_or_else(|panic| resume_unwind(panic))
}

#[cfg(feature = "concurrent")]
#[test]
fn concurrent_disjoint_subpage_protections_survive_the_shared_huge_leaf_split() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    // SAFETY: this fixture edit happens before the table is shared.
    unsafe { seed_pat(table.root_paddr(), address) };
    let table = Arc::new(table);
    let start = Arc::new(Barrier::new(9));
    let workers: Vec<_> = (0..8)
        .map(|worker| {
            let table = table.clone();
            let start = start.clone();
            spawn(move || {
                start.wait();
                let flags = if worker % 2 == 0 {
                    new_flags()
                } else {
                    PTEntryFlags::PRESENT | PTEntryFlags::NX
                };
                let address = VirtAddr::from(BASE + worker * 17 * PAGE);
                let flush = table.mprotect(address, SMALL_LEVEL, flags, true).unwrap();
                let calls = take_flushes();
                if calls.is_empty() {
                    assert_flush_covers(flush, address.bits(), address.bits() + PAGE);
                } else {
                    flush.expect_no_flush();
                    assert_eq!(
                        calls,
                        vec![(
                            FlushScope::Range {
                                start: BASE.into(),
                                end: (BASE + LARGE).into(),
                                level: LARGE_LEVEL,
                            },
                            true
                        )]
                    );
                }
                !calls.is_empty()
            })
        })
        .collect();
    start.wait();
    assert_eq!(workers.into_iter().map(finish).filter(|split| *split).count(), 1);
    for page in 0..512 {
        let old = leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, true);
        let expected = if page % 17 == 0 && page / 17 < 8 {
            let flags = if (page / 17) % 2 == 0 {
                new_flags()
            } else {
                PTEntryFlags::PRESENT | PTEntryFlags::NX
            };
            protected_word(old, flags)
        } else {
            old
        };
        let address = VirtAddr::from(BASE + page * PAGE);
        assert_eq!(table.walk(address).read().raw(), expected, "page {page}");
        assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(FRAME + page * PAGE)));
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    let mut table = Arc::try_unwrap(table).ok().unwrap();
    // SAFETY: all workers joined and this inactive tree owns every subtree.
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn public_snapshots_remain_valid_across_table_publication() {
    for writer_offset in [0, PAGE] {
        let (fixture, table) = resolution_counting_fixture();
        let address = VirtAddr::from(BASE);
        let root = table.root_paddr();
        let before = fixture.arena.allocated();
        let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
        take_resolved_pages();
        let before_publication = table.walk(address);
        assert_eq!(before_publication.level(), PageLevel::Level3);
        assert!(!before_publication.read().present());
        assert_resolved_once(&take_resolved_pages(), root);
        assert_eq!(fixture.arena.allocated(), before);
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst), calls);
        assert!(fixture.locks.0.content.try_lock().is_ok());
        table.map_4k(address + writer_offset, PhysAddr::from(FRAME), old_flags(), false).unwrap();
        assert_eq!(before_publication.level(), PageLevel::Level3);
        assert!(!before_publication.read().present());
        take_resolved_pages();
        let after_publication = table.walk(address);
        let level = after_publication.level();
        let word = after_publication.read().raw();
        assert_eq!(level, SMALL_LEVEL);
        let entry = Entry::from_bits(word);
        assert!(!entry.is_table(level));
        assert_eq!(entry.present(), writer_offset == 0);
        assert_resolved_once(&take_resolved_pages(), root);
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 2);
        assert!(fixture.locks.0.content.try_lock().is_ok());
        assert_eq!(fixture.arena.allocated(), before + 3);
        assert!(fixture.arena.freed().is_empty());
        assert_eq!(table.phys_addr(address + writer_offset), Ok(PhysAddr::from(FRAME)));
        drop(table);
        fixture.assert_all_reclaimed();
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn uncontended_path_publication_resolves_the_root_and_existing_prefix_only_once() {
    for initial_level in [PageLevel::Level3, HUGE_LEVEL] {
        let (fixture, table) = resolution_counting_fixture();
        let address = VirtAddr::from(BASE);
        let root = table.root_paddr();
        if initial_level == HUGE_LEVEL {
            table
                .map(address + HUGE, PhysAddr::from(FRAME), HUGE_LEVEL, old_flags(), false)
                .unwrap();
        }
        let stopping_page = if initial_level == HUGE_LEVEL {
            table.next_table_pa(entry_index(address, PageLevel::Level3)).unwrap()
        } else {
            root
        };
        assert_eq!(table.walk(address).level(), initial_level);
        let before = fixture.arena.allocated();
        let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
        take_resolved_pages();
        table.map_4k(address, PhysAddr::from(OTHER_FRAME), old_flags(), false).unwrap();
        let resolved = take_resolved_pages();
        assert_resolved_once(&resolved, root);
        assert_resolved_once(&resolved, stopping_page);
        assert_eq!(fixture.arena.allocated(), before + initial_level.depth());
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 2);
        assert!(fixture.locks.0.content.try_lock().is_ok());
        assert!(fixture.arena.freed().is_empty());
        assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(OTHER_FRAME)));
        assert_eq!(table.validate_page_table(), Ok(()));
        drop(table);
        fixture.assert_all_reclaimed();
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn a_losing_path_publication_resumes_at_its_deeper_stopping_page_without_rewalking_the_root() {
    let (fixture, table) = resolution_counting_fixture();
    let address = VirtAddr::from(BASE);
    table.map(address + HUGE, PhysAddr::from(FRAME), HUGE_LEVEL, old_flags(), false).unwrap();
    let root = table.root_paddr();
    let stopping_page = table.next_table_pa(entry_index(address, PageLevel::Level3)).unwrap();
    let original = table.walk(address);
    assert_eq!(original.level(), HUGE_LEVEL);
    assert!(!original.read().present());
    let before = fixture.arena.allocated();
    let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
    fixture.check_deallocation_is_unlocked();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || {
            take_resolved_pages();
            let result = table.map_4k(address, PhysAddr::from(OTHER_FRAME), old_flags(), false);
            (result, take_resolved_pages())
        }
    });
    entered.recv_timeout(WAIT).expect("mapping did not reach its publication lock");
    assert_eq!(fixture.arena.allocated(), before + 2);
    assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 1);
    assert!(fixture.locks.0.content.try_lock().is_ok());
    assert!(fixture.arena.freed().is_empty());
    assert_eq!(table.walk(address).level(), original.level());
    assert_eq!(table.walk(address).read().raw(), original.read().raw());
    take_resolved_pages();
    table.map_4k(address + PAGE, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    let winner_resolved = take_resolved_pages();
    assert_eq!(fixture.arena.allocated(), before + 4);
    release.send(()).unwrap();
    let (result, loser_resolved) = finish(worker);
    assert_eq!(result, Ok(()));
    assert_resolved_once(&winner_resolved, root);
    assert_resolved_once(&winner_resolved, stopping_page);
    assert_resolved_once(&loser_resolved, root);
    assert_resolved_once(&loser_resolved, stopping_page);
    assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 4);
    assert!(fixture.locks.0.content.try_lock().is_ok());
    assert_eq!(fixture.arena.allocated(), before + 4);
    assert_eq!(fixture.arena.freed().len(), 2);
    assert_eq!(
        fixture.arena.freed().into_iter().collect::<BTreeSet<_>>(),
        (before..before + 2).map(|page| fixture.arena.base() + page * PAGE).collect()
    );
    assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(OTHER_FRAME)));
    assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME)));
    assert_eq!(table.phys_addr(address + HUGE), Ok(PhysAddr::from(FRAME)));
    assert_eq!(table.validate_page_table(), Ok(()));
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn a_coarse_mapping_losing_to_growth_rejects_an_absent_slot_in_the_finer_subtree() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    let before = fixture.arena.allocated();
    let original = table.walk(address);
    fixture.check_deallocation_is_unlocked();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || table.map_2m(address, PhysAddr::from(OTHER_FRAME), old_flags(), false)
    });
    entered.recv_timeout(WAIT).expect("mapping did not reach its content lock");
    assert_eq!(fixture.arena.allocated(), before + 2);
    assert_eq!(table.walk(address).level(), original.level());
    assert_eq!(table.walk(address).read().raw(), original.read().raw());
    assert!(fixture.arena.freed().is_empty());
    table.map_4k(address + PAGE, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    release.send(()).unwrap();
    assert_eq!(finish(worker), Err(PagingError::NotLeafEntry));
    assert_eq!(
        fixture.arena.freed().into_iter().collect::<BTreeSet<_>>(),
        (before..before + 2).map(|page| fixture.arena.base() + page * PAGE).collect()
    );
    assert_eq!(fixture.arena.freed().len(), 2);
    assert_eq!(table.walk(address).level(), SMALL_LEVEL);
    assert_eq!(table.phys_addr(address), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME)));

    let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
    assert_eq!(
        table.map_2m(address, PhysAddr::from(OTHER_FRAME), old_flags(), false),
        Err(PagingError::NotLeafEntry)
    );
    assert!(matches!(
        table.mprotect(address, LARGE_LEVEL, new_flags(), true),
        Err(PagingError::NotLeafEntry)
    ));
    let (removed, flush) = table.unmap_at(address, LARGE_LEVEL).unwrap();
    assert!(removed.is_none());
    flush.expect_no_flush();
    table.split(address, LARGE_LEVEL, true).unwrap().expect_no_flush();
    assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst), calls);
    assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME)));
    let mut table = Arc::try_unwrap(table).ok().unwrap();
    // SAFETY: the worker joined and this inactive tree is exclusively owned.
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn paused_path_allocations_publish_nothing_and_do_not_block_a_competing_mapper() {
    for target in [SMALL_LEVEL, LARGE_LEVEL] {
        let (fixture, table) = fixture();
        let address = VirtAddr::from(BASE);
        let original = table.walk(address);
        assert_eq!(original.level(), PageLevel::Level3);
        assert!(!original.read().present());
        let needed = original.level().depth() - target.depth();
        let before = fixture.arena.allocated();
        let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
        fixture.check_deallocation_is_unlocked();
        let table = Arc::new(table);
        let (mut entered, mut release) = fixture.pause_next_allocation();
        let worker = spawn({
            let table = table.clone();
            move || table.map(address, PhysAddr::from(OTHER_FRAME), target, old_flags(), false)
        });
        for prepared in 1..=needed {
            entered.recv_timeout(WAIT).expect("mapping did not reach its private allocation");
            assert_eq!(fixture.arena.allocated(), before + prepared);
            assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst), calls);
            assert!(fixture.locks.0.content.try_lock().is_ok());
            assert_eq!(table.walk(address).level(), original.level());
            assert_eq!(table.walk(address).read().raw(), original.read().raw());
            assert_eq!(table.phys_addr(address), Err(PagingError::NotMapped));
            assert!(fixture.arena.freed().is_empty());
            if prepared < needed {
                let next = fixture.pause_next_allocation();
                release.send(()).unwrap();
                (entered, release) = next;
            }
        }
        let winner = spawn({
            let table = table.clone();
            move || table.map_4k(address + PAGE, PhysAddr::from(FRAME), old_flags(), false)
        });
        assert_eq!(finish(winner), Ok(()));
        assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME)));
        assert_eq!(fixture.arena.allocated(), before + needed + 3);
        assert!(fixture.arena.freed().is_empty());
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 2);
        release.send(()).unwrap();
        let result = finish(worker);
        if target == SMALL_LEVEL {
            assert_eq!(result, Ok(()));
            assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(OTHER_FRAME)));
        } else {
            assert_eq!(result, Err(PagingError::NotLeafEntry));
            assert_eq!(table.phys_addr(address), Err(PagingError::NotMapped));
        }
        assert_eq!(fixture.arena.allocated(), before + needed + 3);
        assert_eq!(fixture.arena.freed().len(), needed);
        assert_eq!(
            fixture.arena.freed().into_iter().collect::<BTreeSet<_>>(),
            (before..before + needed).map(|page| fixture.arena.base() + page * PAGE).collect()
        );
        assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME)));
        assert_eq!(table.validate_page_table(), Ok(()));
        let mut table = Arc::try_unwrap(table).ok().unwrap();
        // SAFETY: both workers joined and this inactive tree is exclusively owned.
        unsafe { table.free_children() };
        drop(table);
        fixture.assert_all_reclaimed();
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn a_fine_mapping_losing_to_a_huge_leaf_reclaims_its_preparation_after_unlock() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    table.map(address + HUGE, PhysAddr::from(OTHER_FRAME), HUGE_LEVEL, old_flags(), false).unwrap();
    let original = table.walk(address);
    assert_eq!(original.level(), HUGE_LEVEL);
    assert!(!original.read().present());
    let before = fixture.arena.allocated();
    fixture.check_deallocation_is_unlocked();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || table.map_4k(address + PAGE, PhysAddr::from(OTHER_FRAME), old_flags(), false)
    });
    entered.recv_timeout(WAIT).expect("mapping did not reach its publication lock");
    assert_eq!(fixture.arena.allocated(), before + 2);
    assert_eq!(table.walk(address).level(), original.level());
    assert_eq!(table.walk(address).read().raw(), original.read().raw());
    table.map(address, PhysAddr::from(FRAME), HUGE_LEVEL, old_flags(), false).unwrap();
    release.send(()).unwrap();
    assert_eq!(
        finish(worker),
        Err(PagingError::EntryAlreadyPresent {
            frame: PhysAddr::from(FRAME + PAGE),
            level: HUGE_LEVEL,
        })
    );
    assert_eq!(fixture.arena.allocated(), before + 2);
    assert_eq!(fixture.arena.freed().len(), 2);
    assert_eq!(
        fixture.arena.freed().into_iter().collect::<BTreeSet<_>>(),
        (before..before + 2).map(|page| fixture.arena.base() + page * PAGE).collect()
    );
    assert_eq!(table.walk(address).level(), HUGE_LEVEL);
    assert_eq!(table.phys_addr(address + PAGE), Ok(PhysAddr::from(FRAME + PAGE)));
    assert_eq!(table.phys_addr(address + HUGE), Ok(PhysAddr::from(OTHER_FRAME)));
    assert_eq!(table.validate_page_table(), Ok(()));
    let mut table = Arc::try_unwrap(table).ok().unwrap();
    // SAFETY: the worker joined and this inactive tree is exclusively owned.
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn failed_path_preparation_preserves_the_original_absent_slot_and_installed_tree() {
    for allowed in 0..3 {
        let (fixture, table) = fixture();
        let sibling = VirtAddr::from(BASE + (1usize << 39));
        table.map_4k(sibling, PhysAddr::from(FRAME), old_flags(), false).unwrap();
        let address = VirtAddr::from(BASE);
        // SAFETY: this fixture edit precedes every operation on the exclusively owned tree.
        let (slot, level) = unsafe { leaf_slot(table.root_paddr(), address) };
        assert_eq!(level, PageLevel::Level3);
        let original = Entry::from_bits(PTEntryFlags::WRITABLE.bits() | PTEntryFlags::NX.bits());
        // SAFETY: this absent slot belongs exclusively to the inactive fixture.
        unsafe { Entry::store_entry(slot, original) };
        let before = fixture.arena.allocated();
        let calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
        fixture.check_deallocation_is_unlocked();
        fixture.allow_allocations(allowed);
        assert_eq!(
            table.map_4k(address, PhysAddr::from(OTHER_FRAME), old_flags(), false),
            Err(PagingError::AllocFrame)
        );
        assert_eq!(table.walk(address).level(), level);
        assert_eq!(table.walk(address).read().raw(), original.raw());
        assert_eq!(table.phys_addr(address), Err(PagingError::NotMapped));
        assert_eq!(table.phys_addr(sibling), Ok(PhysAddr::from(FRAME)));
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst), calls);
        assert_eq!(fixture.arena.allocated(), before + allowed);
        assert_eq!(fixture.arena.freed().len(), allowed);
        assert_eq!(
            fixture.arena.freed().into_iter().collect::<BTreeSet<_>>(),
            (before..before + allowed).map(|page| fixture.arena.base() + page * PAGE).collect()
        );
        fixture.allow_allocations(3);
        table.map_4k(address, PhysAddr::from(OTHER_FRAME), old_flags(), false).unwrap();
        assert_eq!(fixture.arena.allocated(), before + allowed + 3);
        assert_eq!(fixture.locks.0.page_calls.load(Ordering::SeqCst) - calls, 2);
        assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(OTHER_FRAME)));
        assert_eq!(table.phys_addr(sibling), Ok(PhysAddr::from(FRAME)));
        assert_eq!(table.validate_page_table(), Ok(()));
        let mut table = table;
        // SAFETY: no worker or hardware user can access this exclusively owned tree.
        unsafe { table.free_children() };
        drop(table);
        fixture.assert_all_reclaimed();
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn unmapping_rechecks_a_split_published_before_lock_acquisition() {
    for target in [None, Some(SMALL_LEVEL), Some(LARGE_LEVEL)] {
        let (fixture, table) = fixture();
        let address = VirtAddr::from(BASE);
        let selected = address + 7 * PAGE;
        table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
        let table = Arc::new(table);
        let (entered, release) = fixture.locks.pause_next();
        let worker = spawn({
            let table = table.clone();
            move || match target {
                Some(level) => table
                    .unmap_at(selected, level)
                    .map(|(entry, flush)| (entry.map(|_| level), flush)),
                None => table.unmap(selected),
            }
        });
        entered.recv_timeout(WAIT).expect("unmapping did not reach its content lock");
        assert_completed(
            table.split(selected, SMALL_LEVEL, true).unwrap(),
            BASE,
            BASE + LARGE,
            LARGE_LEVEL,
        );
        release.send(()).unwrap();
        let (removed, flush) = finish(worker).unwrap();
        if target == Some(LARGE_LEVEL) {
            assert_eq!(removed, None);
            flush.expect_no_flush();
            assert_eq!(table.phys_addr(selected), Ok(PhysAddr::from(FRAME + 7 * PAGE)));
        } else {
            assert_eq!(removed, Some(SMALL_LEVEL));
            assert_flush_covers(flush, selected.bits(), selected.bits() + PAGE);
            assert_eq!(table.phys_addr(selected), Err(PagingError::NotMapped));
        }
        for page in [0, 6, 8, 511] {
            assert_eq!(
                table.phys_addr(address + page * PAGE),
                Ok(PhysAddr::from(FRAME + page * PAGE))
            );
        }
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn a_fine_protection_retries_after_a_split_before_lock_acquisition() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    let selected = address + 7 * PAGE;
    table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || table.mprotect(selected, SMALL_LEVEL, new_flags(), true)
    });
    entered.recv_timeout(WAIT).expect("protection did not reach its content lock");
    assert_completed(
        table.split(selected, SMALL_LEVEL, true).unwrap(),
        BASE,
        BASE + LARGE,
        LARGE_LEVEL,
    );
    release.send(()).unwrap();
    assert_flush_covers(finish(worker).unwrap(), selected.bits(), selected.bits() + PAGE);
    for page in 0..512 {
        let old = leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, false);
        let expected = if page == 7 { protected_word(old, new_flags()) } else { old };
        assert_eq!(table.walk(address + page * PAGE).read().raw(), expected);
    }
}

#[cfg(feature = "concurrent")]
#[test]
fn a_split_waiting_for_its_lock_preserves_a_completed_same_slot_protection() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || {
            let flush = table.split(address + 7 * PAGE, SMALL_LEVEL, true);
            (flush, take_flushes())
        }
    });
    entered.recv_timeout(WAIT).expect("split did not reach its content lock");
    let flush = table.mprotect(address, LARGE_LEVEL, new_flags(), true).unwrap();
    assert_flush_covers(flush, BASE, BASE + LARGE);
    release.send(()).unwrap();
    let (flush, calls) = finish(worker);
    flush.unwrap().expect_no_flush();
    assert_eq!(
        calls,
        vec![(
            FlushScope::Range { start: address, end: address + LARGE, level: LARGE_LEVEL },
            true
        )]
    );
    for page in 0..512 {
        let old = leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, false);
        assert_eq!(
            table.walk(address + page * PAGE).read().raw(),
            protected_word(old, new_flags())
        );
    }
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[cfg(feature = "concurrent")]
#[test]
fn a_coarse_protection_losing_to_a_split_refuses_instead_of_overwriting_children() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    table.map_2m(address, PhysAddr::from(FRAME), old_flags(), false).unwrap();
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || table.mprotect(address, LARGE_LEVEL, new_flags(), true)
    });
    entered.recv_timeout(WAIT).expect("protection did not reach its content lock");
    assert_completed(
        table.split(address + 7 * PAGE, SMALL_LEVEL, true).unwrap(),
        BASE,
        BASE + LARGE,
        LARGE_LEVEL,
    );
    let protected = address + 17 * PAGE;
    let flags = PTEntryFlags::PRESENT | PTEntryFlags::USER;
    assert_flush_covers(
        table.mprotect(protected, SMALL_LEVEL, flags, true).unwrap(),
        protected.bits(),
        protected.bits() + PAGE,
    );
    release.send(()).unwrap();
    assert!(matches!(finish(worker), Err(PagingError::NotLeafEntry)));
    for page in 0..512 {
        let old = leaf_word(FRAME + page * PAGE, SMALL_LEVEL, old_flags(), false, false);
        let expected = if page == 17 { protected_word(old, flags) } else { old };
        assert_eq!(table.walk(address + page * PAGE).level(), SMALL_LEVEL);
        assert_eq!(table.walk(address + page * PAGE).read().raw(), expected);
    }
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[cfg(feature = "concurrent")]
#[test]
fn a_range_observes_finer_levels_after_acquiring_its_whole_domain_guard() {
    let (fixture, table) = fixture();
    let address = VirtAddr::from(BASE);
    table.map(address, PhysAddr::from(FRAME), HUGE_LEVEL, old_flags(), false).unwrap();
    // SAFETY: the fixture edit precedes publication to the worker.
    unsafe { seed_pat(table.root_paddr(), address) };
    let table = Arc::new(table);
    let (entered, release) = fixture.locks.pause_next();
    let worker = spawn({
        let table = table.clone();
        move || table.mprotect_range(address, address + HUGE, new_flags(), true)
    });
    entered.recv_timeout(WAIT).expect("range did not reach its content lock");
    let target = address + LARGE + 7 * PAGE;
    assert_completed(
        table.split(target, SMALL_LEVEL, true).unwrap(),
        BASE,
        BASE + HUGE,
        HUGE_LEVEL,
    );
    release.send(()).unwrap();
    let (result, flush) = finish(worker);
    assert_eq!(result, Ok(()));
    assert_flush_covers(flush, BASE, BASE + HUGE);
    for large in 0..512 {
        let count = if large == 1 { 512 } else { 1 };
        let level = if large == 1 { SMALL_LEVEL } else { LARGE_LEVEL };
        for small in 0..count {
            let offset = large * LARGE + small * PAGE;
            let current = address + offset;
            assert_eq!(table.walk(current).level(), level);
            assert_eq!(
                table.walk(current).read().raw(),
                protected_word(
                    leaf_word(FRAME + offset, level, old_flags(), false, true),
                    new_flags()
                )
            );
            assert_eq!(
                table.phys_addr(current + level.size() - 1),
                Ok(PhysAddr::from(FRAME + offset + level.size() - 1))
            );
        }
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    let mut table = Arc::try_unwrap(table).ok().unwrap();
    // SAFETY: the only worker joined and the tree has never been installed.
    unsafe { table.free_children() };
    drop(table);
    fixture.assert_all_reclaimed();
}

#[cfg(feature = "concurrent")]
#[test]
fn concurrent_split_allocates_once_and_preserves_hardware_ad_accrued_during_preparation() {
    for protect in [false, true] {
        let (fixture, table) = fixture();
        let address = VirtAddr::from(BASE);
        let target_offset = LARGE + 7 * PAGE;
        let target = address + target_offset;
        let history = PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY;
        let flags = old_flags() & !history;
        table.map(address, PhysAddr::from(FRAME), HUGE_LEVEL, flags, false).unwrap();
        // SAFETY: the fixture edit precedes sharing this exclusively owned tree.
        unsafe { seed_pat(table.root_paddr(), address) };
        let original = leaf_word(FRAME, HUGE_LEVEL, flags, false, true);
        assert_eq!(table.walk(address).read().raw(), original);
        // SAFETY: the concurrent tree pins the slot throughout the worker's edit.
        let (slot, level) = unsafe { leaf_slot(table.root_paddr(), address) };
        assert_eq!(level, HUGE_LEVEL);
        let allocated = fixture.arena.allocated();
        assert!(fixture.arena.freed().is_empty());
        let table = Arc::new(table);
        let (entered, release) = fixture.pause_next_allocation();
        let worker = spawn({
            let table = table.clone();
            move || {
                if protect {
                    table.mprotect(target, SMALL_LEVEL, new_flags(), true)
                } else {
                    table.split(target, SMALL_LEVEL, true)
                }
            }
        });
        entered.recv_timeout(WAIT).expect("split did not reach its first private allocation");
        assert_eq!(fixture.arena.allocated(), allocated + 1);
        assert!(fixture.arena.freed().is_empty());
        for offset in [0, PAGE, target_offset, HUGE - 1] {
            let current = address + offset;
            assert_eq!(table.walk(current).level(), HUGE_LEVEL);
            assert_eq!(table.walk(current).read().raw(), original);
            assert_eq!(table.phys_addr(current), Ok(PhysAddr::from(FRAME + offset)));
        }

        // SAFETY: only the concurrent API accesses this aligned, pinned slot.
        // This atomic OR models hardware history updates, never a software mapping change.
        let observed = unsafe { AtomicUsize::from_ptr(slot.cast::<usize>()) }
            .fetch_or(history.bits(), Ordering::SeqCst);
        assert_eq!(observed, original);
        assert_eq!(table.walk(target).level(), HUGE_LEVEL);
        assert_eq!(table.walk(target).read().raw(), original | history.bits());
        assert_eq!(table.phys_addr(target), Ok(PhysAddr::from(FRAME + target_offset)));
        release.send(()).unwrap();

        finish(worker).unwrap().expect_no_flush();
        assert_eq!(fixture.arena.allocated(), allocated + 2);
        assert!(fixture.arena.freed().is_empty(), "private split allocation was retried");
        for large in 0..512 {
            let count = if large == 1 { 512 } else { 1 };
            let level = if large == 1 { SMALL_LEVEL } else { LARGE_LEVEL };
            for small in 0..count {
                let offset = large * LARGE + small * PAGE;
                let current = address + offset;
                let updated = leaf_word(FRAME + offset, level, flags | history, false, true);
                let expected = if protect && offset == target_offset {
                    protected_word(updated, new_flags())
                } else {
                    updated
                };
                assert_eq!(table.walk(current).level(), level);
                assert_eq!(
                    table.walk(current).read().raw(),
                    expected,
                    "protect={protect}, offset={offset:#x}"
                );
                assert_eq!(
                    table.phys_addr(current + level.size() - 1),
                    Ok(PhysAddr::from(FRAME + offset + level.size() - 1))
                );
            }
        }
        // SAFETY: the only worker joined, and this inactive tree is still pinned.
        unsafe { assert_permissive_ancestors(table.root_paddr(), target) };
        assert_eq!(table.validate_page_table(), Ok(()));
        let mut table = Arc::try_unwrap(table).ok().unwrap();
        // SAFETY: no worker or hardware accesses this exclusively owned tree.
        unsafe { table.free_children() };
        drop(table);
        fixture.assert_all_reclaimed();
    }
}

macro_rules! barrier_tests {
    ($module:ident, $fixture:ident) => {
        mod $module {
            #![allow(unused_mut)]

            use super::*;

            #[test]
            fn point_edits_publish_split_before_one_selected_global_barrier() {
                for all_cpus in [false, true] {
                    for level in [LARGE_LEVEL, HUGE_LEVEL] {
                        for operation in 0..4 {
                            let (fixture, mut table) = $fixture();
                            let base = VirtAddr::from(BASE);
                            let offset =
                                if level == HUGE_LEVEL { LARGE + 7 * PAGE } else { 7 * PAGE };
                            let target = base + offset;
                            let initial =
                                old_flags() & !(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY);
                            let shared = operation == 3;
                            table.map(base, FRAME.into(), level, initial, shared).unwrap();
                            // SAFETY: the tree is exclusively owned and all slot accesses are atomic.
                            unsafe { seed_pat(table.root_paddr(), base) };
                            let (slot, observed_level) =
                                unsafe { leaf_slot(table.root_paddr(), target) };
                            assert_eq!(observed_level, level);
                            let allocated = fixture.arena.allocated();
                            let arena = fixture.arena.clone();
                            let slot = slot as usize;
                            set_flush_hook(move |scope, selected| {
                                assert_eq!(selected, all_cpus);
                                assert_eq!(
                                    scope,
                                    FlushScope::Range {
                                        start: base,
                                        end: base + level.size(),
                                        level,
                                    }
                                );
                                let published = unsafe { Entry::load_entry(slot as *const Entry) };
                                assert!(published.present());
                                assert_eq!(published.raw() & PTEntryFlags::HUGE.bits(), 0);
                                assert_eq!(arena.allocated(), allocated + level.depth());
                                assert!(arena.freed().is_empty());
                            });
                            let flush = match operation {
                                0 => table.split(target, SMALL_LEVEL, all_cpus).unwrap(),
                                1 => table
                                    .mprotect(target, SMALL_LEVEL, new_flags(), all_cpus)
                                    .unwrap(),
                                2 => table.set_shared_4k(target, all_cpus).unwrap(),
                                _ => table.set_encrypted_4k(target, all_cpus).unwrap(),
                            };
                            clear_flush_hook();
                            flush.expect_no_flush();
                            assert_eq!(
                                take_flushes(),
                                vec![(
                                    FlushScope::Range {
                                        start: base,
                                        end: base + level.size(),
                                        level,
                                    },
                                    all_cpus
                                )]
                            );
                            assert_eq!(fixture.arena.allocated(), allocated + level.depth());
                            assert!(fixture.arena.freed().is_empty());
                            for current in
                                [0, offset - PAGE, offset, offset + PAGE, level.size() - PAGE]
                            {
                                let address = base + current;
                                let leaf_level = table.walk(address).level();
                                let leaf_offset = current & !(leaf_level.size() - 1);
                                let mut expected = leaf_word(
                                    FRAME + leaf_offset,
                                    leaf_level,
                                    initial,
                                    shared,
                                    true,
                                );
                                if current == offset {
                                    expected = match operation {
                                        1 => protected_word(expected, new_flags()),
                                        2 => expected & !PRIVATE,
                                        3 => expected | PRIVATE,
                                        _ => expected,
                                    };
                                }
                                assert_eq!(
                                    table.walk(address).read().raw(),
                                    expected,
                                    "operation={operation}, level={level:?}, offset={current:#x}"
                                );
                                assert_eq!(table.phys_addr(address), Ok((FRAME + current).into()));
                            }
                            assert_eq!(table.validate_page_table(), Ok(()));
                            unsafe { table.free_children() };
                            drop(table);
                            fixture.assert_all_reclaimed();
                        }
                    }
                }
            }

            #[test]
            fn range_splits_batch_distinct_content_pages_and_both_ends_of_one_huge_leaf() {
                let boundary = 512 * HUGE;
                for (bases, start, end, pages) in [
                    (vec![boundary - HUGE, boundary], boundary - PAGE, boundary + PAGE, 4),
                    (vec![BASE], BASE + PAGE, BASE + 3 * LARGE + PAGE, 3),
                    (vec![BASE], BASE + PAGE, BASE + 3 * PAGE, 2),
                ] {
                    let (fixture, mut table) = $fixture();
                    let mut originals = Vec::new();
                    for (index, base) in bases.iter().copied().enumerate() {
                        table
                            .map(
                                base.into(),
                                (FRAME + index * HUGE).into(),
                                HUGE_LEVEL,
                                old_flags(),
                                index != 0,
                            )
                            .unwrap();
                        unsafe { seed_pat(table.root_paddr(), base.into()) };
                        let (slot, level) = unsafe { leaf_slot(table.root_paddr(), base.into()) };
                        assert_eq!(level, HUGE_LEVEL);
                        originals.push((slot as usize, table.walk(base.into()).read().raw()));
                    }
                    if originals.len() == 2 {
                        assert_ne!(
                            originals[0].0 / PAGE,
                            originals[1].0 / PAGE,
                            "the range must span distinct physical content pages"
                        );
                    }
                    let allocated = fixture.arena.allocated();
                    let arena = fixture.arena.clone();
                    let first = bases[0];
                    let last = bases[bases.len() - 1] + HUGE;
                    let all_cpus = pages != 3;
                    set_flush_hook(move |scope, selected| {
                        assert_eq!(selected, all_cpus);
                        if cfg!(feature = "concurrent") {
                            assert!(matches!(scope, FlushScope::Range { .. }));
                            assert!(arena.allocated() <= allocated + pages);
                            for (slot, _) in &originals {
                                let entry = unsafe { Entry::load_entry(*slot as *const Entry) };
                                assert!(entry.is_leaf(HUGE_LEVEL) || entry.is_table(HUGE_LEVEL));
                            }
                        } else {
                            assert_eq!(
                                scope,
                                FlushScope::Range {
                                    start: first.into(),
                                    end: last.into(),
                                    level: HUGE_LEVEL,
                                }
                            );
                            assert_eq!(arena.allocated(), allocated + pages);
                        }
                    });
                    let (result, flush) =
                        table.mprotect_range(start.into(), end.into(), new_flags(), all_cpus);
                    clear_flush_hook();
                    assert_eq!(result, Ok(()));
                    if cfg!(feature = "concurrent") {
                        discharge(flush);
                        let calls = take_flushes();
                        assert!(!calls.is_empty());
                        assert!(calls.iter().all(|(_, selected)| *selected == all_cpus));
                    } else {
                        flush.expect_no_flush();
                        assert_eq!(take_flushes().len(), 1);
                    }
                    assert_eq!(fixture.arena.allocated(), allocated + pages);
                    for (index, base) in bases.iter().copied().enumerate() {
                        let mut offset = 0;
                        while offset < HUGE {
                            let address = base + offset;
                            let leaf_level = table.walk(address.into()).level();
                            let leaf_offset = offset & !(leaf_level.size() - 1);
                            assert!(!(address < start && start < address + leaf_level.size()));
                            assert!(!(address < end && end < address + leaf_level.size()));
                            let old = leaf_word(
                                FRAME + index * HUGE + leaf_offset,
                                leaf_level,
                                old_flags(),
                                index != 0,
                                true,
                            );
                            let expected = if (start..end).contains(&address) {
                                protected_word(old, new_flags())
                            } else {
                                old
                            };
                            assert_eq!(
                                table.walk(address.into()).read().raw(),
                                expected,
                                "address={address:#x}, range={start:#x}..{end:#x}"
                            );
                            assert_eq!(
                                table.phys_addr((address + leaf_level.size() - 1).into()),
                                Ok((FRAME + index * HUGE + offset + leaf_level.size() - 1).into())
                            );
                            offset += leaf_level.size();
                        }
                    }
                    assert_eq!(table.validate_page_table(), Ok(()));
                    unsafe { table.free_children() };
                    drop(table);
                    fixture.assert_all_reclaimed();
                }
            }

            #[test]
            fn callback_panic_keeps_published_x86_splits_owned_and_valid() {
                for operation in 0..6 {
                    let (fixture, mut table) = $fixture();
                    let base = VirtAddr::from(BASE);
                    let original_count = if operation == 5 { 3 } else { 2 };
                    for index in 0..original_count {
                        table
                            .map(
                                base + index * HUGE,
                                (FRAME + index * HUGE).into(),
                                HUGE_LEVEL,
                                old_flags(),
                                false,
                            )
                            .unwrap();
                        unsafe { seed_pat(table.root_paddr(), base + index * HUGE) };
                    }
                    let originals: Vec<_> = (0..original_count)
                        .map(|index| {
                            let address = base + index * HUGE;
                            let (slot, level) = unsafe { leaf_slot(table.root_paddr(), address) };
                            assert_eq!(level, HUGE_LEVEL);
                            (slot as usize, table.walk(address).read().raw())
                        })
                        .collect();
                    let observed = originals.clone();
                    let allocated = fixture.arena.allocated();
                    let arena = fixture.arena.clone();
                    let valid_before_unlock = Arc::new(AtomicUsize::new(0));
                    let checked = valid_before_unlock.clone();
                    let retained = originals.clone();
                    *fixture.locks.0.before_unlock.lock().unwrap() = Some(Box::new(move || {
                        let valid = retained.iter().all(|(slot, _)| {
                            unsafe { Entry::load_entry(*slot as *const Entry) }.present()
                        });
                        if valid && arena.freed().is_empty() && arena.allocated() > allocated {
                            checked.fetch_add(1, Ordering::SeqCst);
                        }
                    }));
                    set_flush_hook(move |_, _| {
                        for (slot, _) in
                            observed.iter().take(if operation >= 4 { original_count } else { 1 })
                        {
                            assert!(unsafe { Entry::load_entry(*slot as *const Entry) }.present());
                        }
                        panic!("injected synchronous invalidation failure");
                    });
                    let target = base + HUGE - PAGE;
                    let result = catch_unwind(AssertUnwindSafe(|| match operation {
                        0 => table.split(target, SMALL_LEVEL, true).unwrap().expect_no_flush(),
                        1 => table
                            .mprotect(target, SMALL_LEVEL, new_flags(), true)
                            .unwrap()
                            .expect_no_flush(),
                        2 => table.set_shared_4k(target, true).unwrap().expect_no_flush(),
                        3 => table.set_encrypted_4k(target, true).unwrap().expect_no_flush(),
                        _ => {
                            let (result, flush) = table.mprotect_range(
                                target,
                                base + if operation == 5 { 2 * HUGE } else { HUGE } + PAGE,
                                new_flags(),
                                true,
                            );
                            result.unwrap();
                            flush.expect_no_flush();
                        }
                    }));
                    clear_flush_hook();
                    fixture.locks.0.before_unlock.lock().unwrap().take();
                    assert!(result.is_err());
                    assert_eq!(take_flushes().len(), 1);
                    let staging = if cfg!(feature = "concurrent") || operation < 4 { 2 } else { 4 };
                    assert_eq!(fixture.arena.allocated(), allocated + staging);
                    assert!(fixture.arena.freed().is_empty());
                    if fixture.locks.0.page_calls.load(Ordering::SeqCst) != 0 {
                        assert_eq!(
                            valid_before_unlock.load(Ordering::SeqCst),
                            1,
                            "published mappings must stay valid before releasing exclusion"
                        );
                    }
                    for (index, _) in originals.into_iter().enumerate() {
                        let address = base + index * HUGE;
                        let split = if cfg!(feature = "concurrent") {
                            index == 0
                        } else if operation < 4 {
                            index == 0
                        } else if operation == 4 {
                            true
                        } else {
                            index != 1
                        };
                        assert_eq!(
                            table
                                .walk(address + if split && index == 0 { HUGE - PAGE } else { 0 },)
                                .level(),
                            if split { SMALL_LEVEL } else { HUGE_LEVEL }
                        );
                        assert_eq!(
                            table.phys_addr(address + HUGE - 1),
                            Ok((FRAME + (index + 1) * HUGE - 1).into())
                        );
                    }
                    assert_eq!(table.validate_page_table(), Ok(()));
                    unsafe { table.free_children() };
                    drop(table);
                    fixture.assert_all_reclaimed();
                }
            }

            #[test]
            fn unchanged_leaf_edits_neither_flush_synchronously_nor_return_pending_work() {
                let (fixture, mut table) = $fixture();
                let base = VirtAddr::from(BASE);
                table.map_4k(base, FRAME.into(), new_flags(), true).unwrap();
                table.map_4k(base + PAGE, (FRAME + PAGE).into(), new_flags(), false).unwrap();
                let old = table.walk(base).read().raw();
                let encrypted = table.walk(base + PAGE).read().raw();
                let allocated = fixture.arena.allocated();
                table.split(base, SMALL_LEVEL, false).unwrap().expect_no_flush();
                table.mprotect(base, SMALL_LEVEL, new_flags(), false).unwrap().expect_no_flush();
                table.set_shared_4k(base, false).unwrap().expect_no_flush();
                table.set_encrypted_4k(base + PAGE, false).unwrap().expect_no_flush();
                let (result, flush) = table.mprotect_range(base, base + PAGE, new_flags(), false);
                result.unwrap();
                flush.expect_no_flush();
                assert!(take_flushes().is_empty());
                assert_eq!(fixture.arena.allocated(), allocated);
                assert_eq!(table.walk(base).read().raw(), old);
                assert_eq!(table.walk(base + PAGE).read().raw(), encrypted);
            }

            #[test]
            fn overflow_uses_one_whole_tlb_barrier_and_returns_no_pending_split() {
                let (_fixture, mut table) = $fixture();
                let base = VirtAddr::from(usize::MAX & !(HUGE - 1));
                table.map(base, FRAME.into(), HUGE_LEVEL, old_flags(), false).unwrap();
                let (slot, level) = unsafe { leaf_slot(table.root_paddr(), base) };
                assert_eq!(level, HUGE_LEVEL);
                let slot = slot as usize;
                set_flush_hook(move |scope, all_cpus| {
                    assert_eq!(scope, FlushScope::All);
                    assert!(!all_cpus);
                    assert_eq!(
                        unsafe { Entry::load_entry(slot as *const Entry) }.raw()
                            & (PTEntryFlags::PRESENT | PTEntryFlags::HUGE).bits(),
                        PTEntryFlags::PRESENT.bits()
                    );
                });
                table
                    .split(VirtAddr::from(usize::MAX), SMALL_LEVEL, false)
                    .unwrap()
                    .expect_no_flush();
                clear_flush_hook();
                assert_eq!(take_flushes(), vec![(FlushScope::All, false)]);
                assert_eq!(
                    table.phys_addr(VirtAddr::from(usize::MAX)),
                    Ok((FRAME + HUGE - 1).into())
                );
                assert_eq!(table.walk(VirtAddr::from(usize::MAX)).level(), SMALL_LEVEL);
            }

            #[test]
            fn range_preparation_failure_keeps_the_failed_original_huge_leaf_intact() {
                for separate_leaves in [false, true] {
                    let (fixture, mut table) = $fixture();
                    let base = VirtAddr::from(BASE);
                    table.map(base, FRAME.into(), HUGE_LEVEL, old_flags(), false).unwrap();
                    if separate_leaves {
                        table
                            .map(base + HUGE, (FRAME + HUGE).into(), HUGE_LEVEL, old_flags(), false)
                            .unwrap();
                    }
                    let allocated = fixture.arena.allocated();
                    let allowed = if separate_leaves { 3 } else { 1 };
                    fixture.allow_allocations(allowed);
                    let (start, end) = if separate_leaves {
                        (base + HUGE - PAGE, base + HUGE + PAGE)
                    } else {
                        (base + PAGE, base + 3 * LARGE + PAGE)
                    };
                    let (result, flush) = table.mprotect_range(start, end, new_flags(), true);
                    assert_eq!(result, Err(PagingError::AllocFrame));
                    assert_eq!(fixture.arena.allocated(), allocated + allowed);
                    if separate_leaves {
                        assert_completed(flush, BASE, BASE + HUGE, HUGE_LEVEL);
                        assert_eq!(fixture.arena.freed().len(), 1);
                        assert_eq!(
                            table.walk(start).read().raw(),
                            protected_word(
                                leaf_word(
                                    FRAME + HUGE - PAGE,
                                    SMALL_LEVEL,
                                    old_flags(),
                                    false,
                                    false
                                ),
                                new_flags()
                            )
                        );
                    } else {
                        flush.expect_no_flush();
                        assert!(take_flushes().is_empty());
                        assert_eq!(fixture.arena.freed().len(), allowed);
                    }
                    let failed = if separate_leaves { base + HUGE } else { base };
                    assert_eq!(table.walk(failed).level(), HUGE_LEVEL);
                    assert_eq!(
                        table.walk(failed).read().raw(),
                        leaf_word(
                            FRAME + if separate_leaves { HUGE } else { 0 },
                            HUGE_LEVEL,
                            old_flags(),
                            false,
                            false
                        )
                    );
                    assert_eq!(table.validate_page_table(), Ok(()));
                    unsafe { table.free_children() };
                    drop(table);
                    fixture.assert_all_reclaimed();
                }
            }

            #[test]
            fn range_hole_flushes_the_prepared_prefix_once_without_touching_later_mappings() {
                let (fixture, mut table) = $fixture();
                let base = VirtAddr::from(BASE);
                let boundary = base + HUGE;
                table.map(base, FRAME.into(), HUGE_LEVEL, old_flags(), false).unwrap();
                table.map_4k(boundary + PAGE, OTHER_FRAME.into(), old_flags(), true).unwrap();
                let untouched = table.walk(boundary + PAGE).read().raw();
                let (slot, _) = unsafe { leaf_slot(table.root_paddr(), base) };
                let slot = slot as usize;
                set_flush_hook(move |_, _| {
                    assert_eq!(
                        unsafe { Entry::load_entry(slot as *const Entry) }.raw()
                            & (PTEntryFlags::PRESENT | PTEntryFlags::HUGE).bits(),
                        PTEntryFlags::PRESENT.bits()
                    );
                });
                let allocated = fixture.arena.allocated();
                let (result, flush) =
                    table.mprotect_range(boundary - PAGE, boundary + 2 * PAGE, new_flags(), true);
                clear_flush_hook();
                assert_eq!(result, Err(PagingError::NotMapped));
                assert_completed(flush, BASE, BASE + HUGE, HUGE_LEVEL);
                assert_eq!(fixture.arena.allocated(), allocated + 2);
                assert_eq!(
                    table.walk(boundary - PAGE).read().raw(),
                    protected_word(
                        leaf_word(FRAME + HUGE - PAGE, SMALL_LEVEL, old_flags(), false, false),
                        new_flags()
                    )
                );
                assert_eq!(table.phys_addr(boundary), Err(PagingError::NotMapped));
                assert_eq!(table.walk(boundary + PAGE).read().raw(), untouched);
                assert_eq!(table.validate_page_table(), Ok(()));
            }
        }
    };
}

barrier_tests!(selected_controller_barriers, fixture);

#[cfg(feature = "concurrent")]
#[test]
fn paused_point_and_range_barriers_exclude_writers_but_not_lock_free_walkers() {
    for range in [false, true] {
        let (fixture, table) = fixture();
        let boundary = 512 * HUGE;
        let left = VirtAddr::from(boundary - HUGE);
        let right = VirtAddr::from(boundary);
        for (address, frame) in [(left, FRAME), (right, FRAME + HUGE)] {
            table.map(address, frame.into(), HUGE_LEVEL, old_flags(), false).unwrap();
        }
        let table = Arc::new(table);
        let page_calls = fixture.locks.0.page_calls.load(Ordering::SeqCst);
        let (entered, observed) = mpsc::channel();
        let (release, resumed) = mpsc::channel();
        let editor = spawn({
            let table = table.clone();
            let locks = fixture.locks.clone();
            move || {
                let paused = AtomicBool::new(false);
                set_flush_hook(move |_, _| {
                    assert!(matches!(
                        locks.0.content.try_lock(),
                        Err(std::sync::TryLockError::WouldBlock)
                    ));
                    if !paused.swap(true, Ordering::SeqCst) {
                        entered.send(()).unwrap();
                        resumed.recv_timeout(WAIT).expect("edit barrier was not released");
                    }
                });
                let result = if range {
                    table.mprotect_range(right - PAGE, right + PAGE, new_flags(), true)
                } else {
                    (Ok(()), table.split(right + PAGE, SMALL_LEVEL, true).unwrap())
                };
                clear_flush_hook();
                (result, take_flushes())
            }
        });
        observed.recv_timeout(WAIT).expect("edit never reached its synchronous callback");
        assert!(fixture.locks.0.page_calls.load(Ordering::SeqCst) > page_calls);
        let writer = spawn({
            let table = table.clone();
            move || table.map(right, OTHER_FRAME.into(), HUGE_LEVEL, new_flags(), true)
        });
        assert!(matches!(writer.1.try_recv(), Err(mpsc::TryRecvError::Empty)));
        finish(spawn({
            let table = table.clone();
            move || {
                for address in if range {
                    vec![right - PAGE, right, right + PAGE]
                } else {
                    vec![right, right + PAGE]
                } {
                    let expected = if address < right {
                        FRAME + HUGE - PAGE
                    } else {
                        FRAME + HUGE + (address - right)
                    };
                    assert_eq!(table.phys_addr(address), Ok(expected.into()));
                    let snapshot = table.walk(address);
                    assert!(snapshot.read().present());
                }
            }
        }));
        release.send(()).unwrap();
        let ((result, flush), calls) = finish(editor);
        result.unwrap();
        if range {
            discharge(flush);
            assert_eq!(calls.len(), 2);
        } else {
            flush.expect_no_flush();
            assert_eq!(
                calls,
                vec![(
                    FlushScope::Range { start: right, end: right + HUGE, level: HUGE_LEVEL },
                    true
                )]
            );
        }
        assert!(finish(writer).is_err(), "writer replaced a temporarily invalid huge slot");
        assert_eq!(table.phys_addr(right - PAGE), Ok((FRAME + HUGE - PAGE).into()));
        assert_eq!(table.phys_addr(right), Ok((FRAME + HUGE).into()));
        assert_eq!(table.validate_page_table(), Ok(()));
    }
}

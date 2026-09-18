//! Concurrent entry updates, lock-free snapshots, and externally excluded reclamation.
#![cfg(feature = "concurrent")]

mod common;

use std::cell::Cell;
use std::collections::BTreeSet;
use std::ops::{Deref, DerefMut, Range};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Barrier, Mutex, MutexGuard, RwLock, TryLockError};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use common::{flags, load_entry, Allocator, Arena, Host, RebasedAllocator, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::frame::PhysFrame;
use paging::level::{Lvl, PageLevel};
use paging::os_contract::{DirectMappedAllocator, MapRegionError, PagingError};
use paging::page::Page;
use paging::pagetable::{LockSpec, PageTable};
use paging::ptpage::PTPage;
use paging::sizes::{entry_index, Size4KiB};
use paging::tlb::MayNeedFlush;
use paging::{FlushScope, PTEntryFlags, X86Paging, X86TlbFlushTok};

const PAGE: usize = 4096;
const LARGE: usize = 2 * 1024 * 1024;
const HUGE: usize = 1024 * 1024 * 1024;
const BASE: usize = 0x4000_0000;
const WAIT: Duration = Duration::from_secs(10);
const SMALL_LEVEL: PageLevel = PageLevel::Level0;
const LARGE_LEVEL: PageLevel = PageLevel::Level1;
const HUGE_LEVEL: PageLevel = PageLevel::Level2;

type Table = PageTable<X86Paging<Host>, Allocator, Lvl<3>, Locks>;
type Worker<T> = (JoinHandle<()>, mpsc::Receiver<thread::Result<T>>);

thread_local! {
    static HOLDING_CONTENT_LOCK: Cell<bool> = const { Cell::new(false) };
}

struct LockState<T> {
    pages: Range<usize>,
    stripes: Vec<Mutex<T>>,
    calls: AtomicUsize,
    unlocks: AtomicUsize,
    keys: Mutex<BTreeSet<usize>>,
    notify: Mutex<Option<mpsc::Sender<PhysAddr>>>,
}

struct Locks<T = ()>(Arc<LockState<T>>);

impl<T> Clone for Locks<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Locks<T> {
    fn new(pages: Range<usize>, stripes: usize) -> Self
    where
        T: Default,
    {
        assert!(stripes > 0);
        Self(Arc::new(LockState {
            pages,
            stripes: (0..stripes).map(|_| Mutex::new(T::default())).collect(),
            calls: AtomicUsize::new(0),
            unlocks: AtomicUsize::new(0),
            keys: Mutex::new(BTreeSet::new()),
            notify: Mutex::new(None),
        }))
    }

    fn assert_balanced(&self) {
        assert_eq!(self.0.calls.load(Ordering::Relaxed), self.0.unlocks.load(Ordering::Relaxed));
        assert!(self.0.calls.load(Ordering::Relaxed) > 0);
        for lock in &self.0.stripes {
            assert!(lock.try_lock().is_ok(), "a completed operation retained its guard");
        }
    }
}

struct CountedGuard<'a, T> {
    inner: MutexGuard<'a, T>,
    state: &'a LockState<T>,
}

impl<T> Deref for CountedGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T> DerefMut for CountedGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

impl<T> Drop for CountedGuard<'_, T> {
    fn drop(&mut self) {
        self.state.unlocks.fetch_add(1, Ordering::Relaxed);
        HOLDING_CONTENT_LOCK.with(|held| held.set(false));
    }
}

// SAFETY: stable physical keys select stable mutexes, including when every key
// aliases one mutex. Dropping the wrapped MutexGuard releases it without panicking.
unsafe impl<T> LockSpec<T> for Locks<T> {
    type Guard<'a>
        = CountedGuard<'a, T>
    where
        T: 'a;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_> {
        HOLDING_CONTENT_LOCK.with(|held| {
            assert!(!held.get(), "paging nested content locks");
        });
        assert!(page.is_aligned(PAGE));
        assert!(self.0.pages.contains(&page.bits()), "not a physical table-page key: {page:?}");
        self.0.keys.lock().unwrap().insert(page.bits());
        self.0.calls.fetch_add(1, Ordering::Relaxed);
        if let Some(notify) = self.0.notify.lock().unwrap().as_ref() {
            let _ = notify.send(page);
        }
        let stripe = (page.bits() / PAGE) % self.0.stripes.len();
        let guard = self.0.stripes[stripe].lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        HOLDING_CONTENT_LOCK.with(|held| held.set(true));
        CountedGuard { inner: guard, state: &self.0 }
    }
}

fn fixture(stripes: usize) -> (Arc<Arena>, Table, Locks) {
    let arena = Arena::new(ARENA);
    let locks = Locks::new(arena.base()..arena.base() + arena.len(), stripes);
    let table = Table::new(locks.clone(), flags()).unwrap();
    assert_eq!(locks.0.calls.load(Ordering::Relaxed), 0, "construction acquired a content lock");
    assert_eq!(locks.0.unlocks.load(Ordering::Relaxed), 0);
    (arena, table, locks)
}

fn discharge(flush: MayNeedFlush<X86TlbFlushTok<Host>>) {
    // SAFETY: these host tables are never installed in hardware.
    unsafe { flush.ignore() };
}

fn spawn<T: Send + 'static>(job: impl FnOnce() -> T + Send + 'static) -> Worker<T> {
    let (send, receive) = mpsc::channel();
    let handle = thread::spawn(move || {
        let result = catch_unwind(AssertUnwindSafe(job));
        let _ = send.send(result);
    });
    (handle, receive)
}

fn finish<T>((handle, receive): Worker<T>) -> T {
    let result = receive.recv_timeout(WAIT).expect("worker did not finish within the deadline");
    handle.join().unwrap();
    result.unwrap_or_else(|panic| resume_unwind(panic))
}

fn race<T: Send + 'static>(
    count: usize,
    job: impl Fn(usize) -> T + Send + Sync + 'static,
) -> Vec<T> {
    let start = Arc::new(Barrier::new(count + 1));
    let job = Arc::new(job);
    let workers: Vec<_> = (0..count)
        .map(|index| {
            let start = start.clone();
            let job = job.clone();
            spawn(move || {
                start.wait();
                job(index)
            })
        })
        .collect();
    start.wait();
    workers.into_iter().map(finish).collect()
}

fn leaf_word(frame: usize, flags: PTEntryFlags, level: PageLevel) -> usize {
    let flags = if level == SMALL_LEVEL { flags } else { flags | PTEntryFlags::HUGE };
    PTEntry::<X86Paging<Host>>::new(PhysAddr::from(frame), flags).raw()
}

fn assert_freed_once(arena: &Arena, expected: usize) {
    let freed = arena.freed();
    assert_eq!(freed.len(), expected);
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), expected);
}

#[test]
fn nonunit_lock_metadata_is_mutably_accessible_and_survives_paging_operations() {
    #[derive(Default)]
    struct Metadata {
        root: Option<PhysAddr>,
        visits: usize,
    }

    let arena = Arena::new(ARENA);
    let locks = Locks::<Metadata>::new(arena.base()..arena.base() + arena.len(), 1);
    let table = Arc::new(
        PageTable::<X86Paging<Host>, Allocator, Lvl<3>, Locks<Metadata>, Metadata>::new(
            locks.clone(),
            flags(),
        )
        .unwrap(),
    );
    let root = table.root_paddr();
    {
        let mut guard = locks.lock(root);
        assert!(guard.root.is_none());
        guard.root = Some(root);
        guard.visits += 1;
    }
    race(8, {
        let table = table.clone();
        let locks = locks.clone();
        let frame = arena.base();
        move |worker| {
            let address = VirtAddr::from(BASE + worker * PAGE);
            table
                .map(
                    common::page_4k(address),
                    common::frame_4k(PhysAddr::from(frame + worker * PAGE)),
                    flags(),
                    false,
                )
                .unwrap();
            let mut guard = locks.lock(root);
            assert_eq!(guard.root, Some(root));
            guard.visits += 1;
        }
    });
    {
        let guard = locks.lock(root);
        assert_eq!(guard.root, Some(root));
        assert_eq!(guard.visits, 9);
    }
    for worker in 0..8 {
        assert_eq!(
            table.phys_addr(VirtAddr::from(BASE + worker * PAGE)),
            Ok(PhysAddr::from(arena.base() + worker * PAGE))
        );
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn competing_maps_have_one_winner_and_report_the_leaf_level() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let base = arena.base();
        let before = arena.allocated();
        let results = race(12, {
            let table = table.clone();
            move |index| {
                table.map(
                    common::page_4k(VirtAddr::from(BASE)),
                    common::frame_4k(PhysAddr::from(base + index * PAGE)),
                    flags(),
                    false,
                )
            }
        });
        let winners: Vec<_> = results.iter().enumerate().filter(|(_, r)| r.is_ok()).collect();
        assert_eq!(winners.len(), 1);
        let winner = PhysAddr::from(base + winners[0].0 * PAGE);
        for (index, result) in results.iter().enumerate() {
            if index != winners[0].0 {
                assert_eq!(*result, Err(PagingError::EntryAlreadyPresent { level: SMALL_LEVEL }));
            }
        }
        assert_eq!(table.phys_addr(VirtAddr::from(BASE + 137)), Ok(winner + 137usize));
        assert_eq!(table.validate_page_table(), Ok(()));
        assert_eq!(arena.allocated() - arena.freed().len(), before + 3);
        locks.assert_balanced();
        let mut table = Arc::try_unwrap(table).ok().unwrap();
        // SAFETY: every worker joined and this inactive tree is exclusively owned.
        unsafe { table.free_children() };
        drop(table);
        assert_freed_once(&arena, arena.allocated());
    }
}

#[test]
fn competing_ranges_allow_only_one_mapping() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let base = arena.base();
        let before = arena.allocated();
        let results = race(12, {
            let table = table.clone();
            move |index| {
                let page = Page::<Size4KiB>::containing_address(VirtAddr::from(BASE));
                let mut frames = core::iter::once(
                    PhysFrame::<Size4KiB>::from_start_address(PhysAddr::from(
                        base + (index % 2) * PAGE,
                    ))
                    .unwrap(),
                );
                table.map_region(Page::range_inclusive(page, page), &mut frames, flags())
            }
        });
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        assert_eq!(
            results
                .iter()
                .filter(|result| {
                    **result
                        == Err(MapRegionError {
                            error: PagingError::EntryAlreadyPresent { level: SMALL_LEVEL },
                            unmapped_pages: 1,
                        })
                })
                .count(),
            11
        );
        assert_eq!(table.validate_page_table(), Ok(()));
        assert_eq!(arena.allocated() - arena.freed().len(), before + 3);
        locks.assert_balanced();
        let mut table = Arc::try_unwrap(table).ok().unwrap();
        // SAFETY: every worker joined and this inactive tree is exclusively owned.
        unsafe { table.free_children() };
        drop(table);
        assert_freed_once(&arena, arena.allocated());
    }
}

#[test]
fn range_frame_iteration_happens_without_a_content_guard() {
    let (arena, mut table, locks) = fixture(1);
    let start = Page::<Size4KiB>::containing_address(VirtAddr::from(BASE));
    let range = Page::range_inclusive(start, start + 1);
    let mut frames = (0..2).map(|offset| {
        HOLDING_CONTENT_LOCK.with(|held| {
            assert!(!held.get(), "frame iterator called under the content lock");
        });
        PhysFrame::from_start_address(PhysAddr::from(arena.base() + offset * PAGE)).unwrap()
    });

    assert_eq!(table.map_region(range, &mut frames, flags()), Ok(()));
    locks.assert_balanced();
    // SAFETY: this inactive tree is exclusively owned.
    unsafe { table.free_children() };
    drop(table);
    assert_freed_once(&arena, arena.allocated());
}

#[test]
fn disjoint_maps_racing_to_grow_common_paths_are_all_preserved() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let before = arena.allocated();
        let frame = arena.base();
        race(8, {
            let table = table.clone();
            move |worker| {
                for branch in 0..12 {
                    for page in 0..4 {
                        let offset = branch * LARGE + (page * 8 + worker) * PAGE;
                        table
                            .map(
                                common::page_4k(VirtAddr::from(BASE + offset)),
                                common::frame_4k(PhysAddr::from(
                                    frame + (page * 8 + worker) * PAGE,
                                )),
                                flags(),
                                false,
                            )
                            .unwrap();
                    }
                }
            }
        });
        for branch in 0..12 {
            for page in 0..32 {
                assert_eq!(
                    table.phys_addr(VirtAddr::from(BASE + branch * LARGE + page * PAGE + 31)),
                    Ok(PhysAddr::from(frame + page * PAGE + 31))
                );
            }
        }
        assert_eq!(arena.allocated() - before - arena.freed().len(), 14);
        assert_eq!(table.validate_page_table(), Ok(()));
        locks.assert_balanced();
        let mut table = Arc::try_unwrap(table).ok().unwrap();
        // SAFETY: every worker joined and this inactive tree is exclusively owned.
        unsafe { table.free_children() };
        drop(table);
        assert_freed_once(&arena, arena.allocated());
    }
}

#[test]
fn competing_unmaps_return_the_original_entry_exactly_once() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let frame = PhysAddr::from(arena.base());
        let vaddr = VirtAddr::from(BASE);
        table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
        let expected = table.walk(vaddr).read().raw();
        let before = arena.allocated();
        let results = race(12, {
            let table = table.clone();
            move |_| {
                let (entry, flush) = table.unmap(common::page_4k(vaddr), true).unwrap();
                assert_eq!(flush.is_pending(), entry.is_some());
                discharge(flush);
                entry.map(|entry| entry.raw())
            }
        });
        assert_eq!(results.iter().filter_map(|entry| *entry).collect::<Vec<_>>(), vec![expected]);
        assert!(table.walk(vaddr).read().is_clear());
        assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
        assert_eq!(arena.allocated(), before);
        assert!(arena.freed().is_empty(), "shared operations cannot reclaim table pages");
        locks.assert_balanced();
    }
}

#[test]
fn overlapping_updates_expose_only_absence_or_complete_mapping_snapshots() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let frames = [arena.base(), arena.base() + PAGE];
        let permissions = [flags(), PTEntryFlags::exec() | PTEntryFlags::USER];
        let words = [
            leaf_word(frames[0], permissions[0], SMALL_LEVEL),
            leaf_word(frames[1], permissions[1], SMALL_LEVEL),
        ];
        let vaddr = VirtAddr::from(BASE);
        table
            .map(
                common::page_4k(vaddr),
                common::frame_4k(PhysAddr::from(frames[0])),
                permissions[0],
                false,
            )
            .unwrap();
        discharge(table.unmap(common::page_4k(vaddr), true).unwrap().1);
        race(6, {
            let table = table.clone();
            move |worker| {
                for iteration in 0..512 {
                    if worker < 2 {
                        match table.map(
                            common::page_4k(vaddr),
                            common::frame_4k(PhysAddr::from(frames[worker])),
                            permissions[worker],
                            false,
                        ) {
                            Ok(()) => {}
                            Err(PagingError::EntryAlreadyPresent { level: SMALL_LEVEL }) => {}
                            result => panic!("unexpected map result: {result:?}"),
                        }
                        let (entry, flush) = table.unmap(common::page_4k(vaddr), true).unwrap();
                        if let Some(entry) = entry {
                            assert!(words.contains(&entry.raw()));
                        }
                        discharge(flush);
                    } else {
                        let snapshot = table.walk(vaddr + 137usize);
                        let word = snapshot.read().raw();
                        assert_eq!(snapshot.level(), SMALL_LEVEL);
                        assert!(word == 0 || words.contains(&word), "torn entry: {word:#x}");
                        match table.phys_addr(vaddr + 137usize) {
                            Ok(frame) => {
                                assert!(frames.iter().any(|base| frame.bits() == base + 137))
                            }
                            Err(error) => assert_eq!(error, PagingError::NotMapped),
                        }
                        if iteration % 16 == 0 {
                            thread::yield_now();
                        }
                        assert_eq!(
                            snapshot.read().raw(),
                            word,
                            "a snapshot changed after its walk"
                        );
                    }
                }
            }
        });
        assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
        assert_eq!(table.validate_page_table(), Ok(()));
        assert!(arena.freed().is_empty());
        locks.assert_balanced();
    }
}

#[test]
fn walks_finish_while_a_writer_is_blocked_on_the_content_lock() {
    let (arena, table, locks) = fixture(1);
    let table = Arc::new(table);
    let vaddr = VirtAddr::from(BASE);
    let frame = PhysAddr::from(arena.base());
    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    let old = table.walk(vaddr);
    let expected = old.read().raw();
    let held = locks.0.stripes[0].lock().unwrap();
    let (attempted, attempts) = mpsc::channel();
    *locks.0.notify.lock().unwrap() = Some(attempted);
    let writer = spawn({
        let table = table.clone();
        move || {
            discharge(table.unmap(common::page_4k(vaddr), true).unwrap().1);
            table
                .map(
                    common::page_4k(vaddr),
                    common::frame_4k(frame + PAGE),
                    PTEntryFlags::exec(),
                    false,
                )
                .unwrap();
        }
    });
    let attempt = attempts.recv_timeout(WAIT);
    let calls = locks.0.calls.load(Ordering::Relaxed);
    let reader = spawn({
        let table = table.clone();
        move || {
            let snapshot = table.walk(vaddr + 137usize);
            (
                snapshot.read().raw(),
                snapshot.level(),
                table.phys_addr(vaddr + 137usize),
                table.translate(vaddr).map(|translation| translation.size()),
                table.walk(vaddr + LARGE).read().is_clear(),
            )
        }
    });
    let observed = reader.1.recv_timeout(WAIT);
    let calls_after_read = locks.0.calls.load(Ordering::Relaxed);
    drop(held);
    *locks.0.notify.lock().unwrap() = None;
    finish(writer);
    attempt.expect("writer never attempted its content lock");
    let observed = observed.expect("walk blocked behind a content lock").unwrap();
    reader.0.join().unwrap();
    assert_eq!(observed, (expected, SMALL_LEVEL, Ok(frame + 137usize), Ok(PAGE), true));
    assert_eq!(calls_after_read, calls, "read-only walks acquired a content lock");
    assert_eq!(old.read().raw(), expected);
    assert_eq!(table.phys_addr(vaddr), Ok(frame + PAGE));
    locks.assert_balanced();
}

#[test]
fn splitting_a_gibibyte_exposes_only_complete_children_or_the_invalid_original_leaf() {
    for stripes in [1, 7] {
        let (_arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let frame = 2 * HUGE;
        let permissions =
            flags() | PTEntryFlags::USER | PTEntryFlags::NO_CACHE | PTEntryFlags::WRITE_THROUGH;
        let target = 3 * LARGE + PAGE;
        map_at!(table, VirtAddr::from(BASE), PhysAddr::from(frame), HUGE_LEVEL, permissions, false)
            .unwrap();
        let old = table.walk(VirtAddr::from(BASE + target));
        race(5, {
            let table = table.clone();
            move |worker| {
                if worker == 0 {
                    discharge(
                        split_at!(table, VirtAddr::from(BASE + target), SMALL_LEVEL, true).unwrap(),
                    );
                } else {
                    for iteration in 0..256 {
                        for offset in [0, target - PAGE, target + 137, target + PAGE, HUGE - 1] {
                            let snapshot = table.walk(VirtAddr::from(BASE + offset));
                            let level = snapshot.level();
                            assert!([SMALL_LEVEL, LARGE_LEVEL, HUGE_LEVEL].contains(&level));
                            let mapped = (frame + offset) & !(level.size() - 1);
                            if snapshot.read().present() {
                                assert_eq!(
                                    snapshot.read().raw(),
                                    leaf_word(mapped, permissions, level)
                                );
                            } else {
                                assert_eq!(level, HUGE_LEVEL);
                                assert_eq!(
                                    snapshot.read().raw(),
                                    leaf_word(frame, permissions, HUGE_LEVEL)
                                        & !PTEntryFlags::PRESENT.bits()
                                );
                            }
                            match table.phys_addr(VirtAddr::from(BASE + offset)) {
                                Ok(actual) => assert_eq!(actual, PhysAddr::from(frame + offset)),
                                Err(PagingError::NotMapped) => {}
                                other => panic!("unexpected split snapshot: {other:?}"),
                            }
                        }
                        if iteration % 16 == 0 {
                            thread::yield_now();
                        }
                    }
                }
            }
        });
        assert_eq!(old.level(), HUGE_LEVEL);
        assert_eq!(old.read().raw(), leaf_word(frame, permissions, HUGE_LEVEL));
        for page in 0..512 {
            let offset = 3 * LARGE + page * PAGE;
            let snapshot = table.walk(VirtAddr::from(BASE + offset));
            assert_eq!(snapshot.level(), SMALL_LEVEL);
            assert_eq!(snapshot.read().raw(), leaf_word(frame + offset, permissions, SMALL_LEVEL));
        }
        for page in 0..512 {
            if page != 3 {
                let offset = page * LARGE;
                let snapshot = table.walk(VirtAddr::from(BASE + offset));
                assert_eq!(snapshot.level(), LARGE_LEVEL);
                assert_eq!(
                    snapshot.read().raw(),
                    leaf_word(frame + offset, permissions, LARGE_LEVEL)
                );
            }
        }
        discharge(split_at!(table, VirtAddr::from(BASE + target), HUGE_LEVEL, true).unwrap());
        assert_eq!(
            table.walk(VirtAddr::from(BASE + target)).level(),
            SMALL_LEVEL,
            "split must not collapse"
        );
        let start = VirtAddr::from(BASE + target);
        let (_, pending) = table.unmap_region(start, start + 3 * PAGE).unwrap();
        discharge(pending);
        for page in 0..512 {
            let offset = 3 * LARGE + page * PAGE;
            let expected = if (1..4).contains(&page) {
                Err(PagingError::NotMapped)
            } else {
                Ok(PhysAddr::from(frame + offset))
            };
            assert_eq!(table.phys_addr(VirtAddr::from(BASE + offset)), expected);
        }
        assert_eq!(table.validate_page_table(), Ok(()));
        locks.assert_balanced();
    }
}

#[test]
fn split_parents_do_not_retain_restrictive_leaf_permissions() {
    let (_arena, table, locks) = fixture(1);
    let frame = PhysAddr::from(2 * HUGE);
    let address = VirtAddr::from(BASE + 3 * LARGE + PAGE);
    let original = PTEntryFlags::data_ro();
    map_at!(table, VirtAddr::from(BASE), frame, HUGE_LEVEL, original, false).unwrap();
    discharge(split_at!(table, address, SMALL_LEVEL, true).unwrap());
    let mut page =
        <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(table.root_paddr())
            .as_ptr::<PTPage<X86Paging<Host>, Allocator>>();
    for level in [PageLevel::Level3, HUGE_LEVEL, LARGE_LEVEL] {
        let pte = PTPage::entry_ptr(page, entry_index(address, level));
        // SAFETY: the table borrow pins this path; the atomic load creates no live PTE reference.
        let entry = unsafe { load_entry(pte) };
        assert!(entry.is_table(level));
        assert!(entry.writable(), "a split parent retained the huge leaf's read-only bit");
        assert!(entry.user(), "a split parent retained the huge leaf's supervisor-only bit");
        assert!(!entry.flags().nx(), "a split parent retained the huge leaf's execute restriction");
        page = <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(PhysAddr::from(
            entry.address(),
        ))
        .as_ptr();
    }
    let mapped = frame + 3 * LARGE + PAGE;
    assert_eq!(table.walk(address).read().raw(), leaf_word(mapped.bits(), original, SMALL_LEVEL));
    discharge(table.unmap(common::page_4k(address), true).unwrap().1);
    let writable_user_code = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER;
    table
        .map(common::page_4k(address), common::frame_4k(mapped), writable_user_code, false)
        .unwrap();
    assert_eq!(
        table.walk(address).read().raw(),
        leaf_word(mapped.bits(), writable_user_code, SMALL_LEVEL)
    );
    assert_eq!(
        table.walk(address + PAGE).read().raw(),
        leaf_word(mapped.bits() + PAGE, original, SMALL_LEVEL)
    );
    assert_eq!(
        table.walk(VirtAddr::from(BASE)).read().raw(),
        leaf_word(frame.bits(), original, LARGE_LEVEL)
    );
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn huge_pat_survives_both_split_steps_without_becoming_a_physical_address_bit() {
    const HUGE_PAT: usize = 1 << 12;
    const SMALL_PAT: usize = 1 << 7;

    let (_arena, table, locks) = fixture(1);
    let address = VirtAddr::from(BASE);
    let frame = PhysAddr::from(2 * HUGE);
    map_at!(table, address, frame, HUGE_LEVEL, flags(), false).unwrap();
    let root_pte = PTPage::<X86Paging<Host>, Allocator>::entry_ptr(
        <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(table.root_paddr())
            .as_ptr(),
        entry_index(address, PageLevel::Level3),
    );
    // SAFETY: this inactive tree is exclusively owned, and the root remains allocated.
    let parent = unsafe { load_entry(root_pte) };
    assert!(parent.is_table(PageLevel::Level3));
    let huge_pte = PTPage::<X86Paging<Host>, Allocator>::entry_ptr_mut(
        <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(PhysAddr::from(
            parent.address(),
        ))
        .as_mut_ptr(),
        entry_index(address, HUGE_LEVEL),
    );
    // SAFETY: Host identity-maps this child, and no other thread or hardware uses the tree.
    unsafe {
        let leaf = load_entry(huge_pte);
        assert!(leaf.is_leaf(HUGE_LEVEL));
        (&*huge_pte.cast::<AtomicUsize>()).store(leaf.raw() | HUGE_PAT, Ordering::Release);
    }
    for offset in [0, PAGE, LARGE + PAGE, HUGE - 1] {
        assert_eq!(table.phys_addr(address + offset), Ok(frame + offset));
    }
    assert_eq!(
        table.map(common::page_4k(address), common::frame_4k(frame), flags(), false),
        Err(PagingError::EntryAlreadyPresent { level: HUGE_LEVEL })
    );
    let target = address + 3 * LARGE + PAGE;
    discharge(split_at!(table, target, LARGE_LEVEL, true).unwrap());
    for page in 0..512 {
        let offset = page * LARGE;
        let snapshot = table.walk(address + offset);
        assert_eq!(snapshot.level(), LARGE_LEVEL);
        assert_eq!(
            snapshot.read().raw(),
            leaf_word(frame.bits() + offset, flags(), LARGE_LEVEL) | HUGE_PAT
        );
        assert_eq!(table.phys_addr(address + offset), Ok(frame + offset));
    }
    discharge(split_at!(table, target, SMALL_LEVEL, true).unwrap());
    for page in 0..512 {
        let offset = 3 * LARGE + page * PAGE;
        let snapshot = table.walk(address + offset);
        assert_eq!(snapshot.level(), SMALL_LEVEL);
        assert_eq!(
            snapshot.read().raw(),
            leaf_word(frame.bits() + offset, flags(), SMALL_LEVEL) | SMALL_PAT
        );
        assert_eq!(table.phys_addr(address + offset + 137usize), Ok(frame + offset + 137usize));
    }
    let sibling = table.walk(address);
    assert_eq!(sibling.level(), LARGE_LEVEL);
    assert_eq!(sibling.read().raw(), leaf_word(frame.bits(), flags(), LARGE_LEVEL) | HUGE_PAT);
    discharge(table.set_shared(common::page_4k(target), true).unwrap());
    discharge(table.set_private(common::page_4k(target), true).unwrap());
    assert_eq!(
        table.walk(target).read().raw(),
        leaf_word(frame.bits() + 3 * LARGE + PAGE, flags(), SMALL_LEVEL) | SMALL_PAT
    );
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn sharing_top_entries_preserves_their_complete_permission_bits() {
    let (arena, table, locks) = fixture(1);
    let address = VirtAddr::from(BASE);
    let frame = PhysAddr::from(arena.base());
    table.map(common::page_4k(address), common::frame_4k(frame), flags(), false).unwrap();
    let index = entry_index(address, PageLevel::Level3);
    let original_pte = PTPage::<X86Paging<Host>, Allocator>::entry_ptr_mut(
        <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(table.root_paddr())
            .as_mut_ptr(),
        index,
    );
    // SAFETY: this inactive tree has no competing software or hardware users.
    let restrictive = unsafe {
        let original = load_entry(original_pte);
        let flags = PTEntryFlags::NX | PTEntryFlags::NO_CACHE | PTEntryFlags::WRITE_THROUGH;
        let cleared = PTEntryFlags::WRITABLE | PTEntryFlags::USER;
        let mut entry = original;
        entry.set_flags(flags);
        entry.clear_flags(cleared);
        (&*original_pte.cast::<AtomicUsize>()).store(entry.raw(), Ordering::Release);
        entry
    };
    // SAFETY: both roots use identical virtual prefixes and the same lock domain.
    // The shared children remain allocated until both roots have been dropped.
    let shared = unsafe { Table::new_from_sharing_top::<0, 512>(locks.clone(), &table) }.unwrap();
    let shared_pte = PTPage::<X86Paging<Host>, Allocator>::entry_ptr(
        <Allocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(shared.root_paddr())
            .as_ptr(),
        index,
    );
    // SAFETY: the shared root is allocated and neither root has competing writers.
    let copied = unsafe { load_entry(shared_pte) };
    assert_eq!(copied.raw(), restrictive.raw());
    assert!(!copied.writable());
    assert!(!copied.user());
    assert!(copied.flags().nx());
    assert_eq!(shared.next_table_pa(index), table.next_table_pa(index));
    assert_eq!(shared.phys_addr(address), Ok(frame));
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(shared.validate_page_table(), Ok(()));
    assert!(arena.freed().is_empty());
    let shared_root = shared.root_paddr();
    drop(shared);
    assert_eq!(arena.freed(), vec![shared_root.bits()]);
    locks.assert_balanced();
}

#[test]
fn mapping_a_five_level_path_publishes_under_one_lock() {
    let arena = Arena::new(ARENA);
    let locks = Locks::<()>::new(arena.base()..arena.base() + arena.len(), 1);
    let mut table =
        PageTable::<X86Paging<Host>, Allocator, Lvl<4>, Locks>::new(locks.clone(), flags())
            .unwrap();
    let address = VirtAddr::from(0xffff_8000_4000_0000usize);
    let frame = PhysAddr::from(arena.base());
    assert_eq!(table.walk(address).level(), PageLevel::Level4);
    assert!(!table.walk(address).read().present());
    let before = locks.0.calls.load(Ordering::Relaxed);
    table.map(common::page_4k(address), common::frame_4k(frame), flags(), false).unwrap();
    assert_eq!(locks.0.calls.load(Ordering::Relaxed) - before, 1);
    assert_eq!(table.walk(address).level(), SMALL_LEVEL);
    assert_eq!(table.phys_addr(address), Ok(frame));
    locks.assert_balanced();
    // SAFETY: this inactive tree is exclusively owned and no view has escaped.
    unsafe { table.free_children() };
}

#[test]
fn split_and_unmap_races_follow_per_entry_serial_semantics() {
    for stripes in [1, 7] {
        let (arena, table, locks) = fixture(stripes);
        let table = Arc::new(table);
        let frame = arena.base();
        const SLOTS: usize = 48;
        for entry_index in 0..SLOTS {
            table
                .map(
                    common::page_2m(VirtAddr::from(BASE + entry_index * LARGE)),
                    common::frame_2m(PhysAddr::from(frame + entry_index * LARGE)),
                    flags(),
                    false,
                )
                .unwrap();
        }
        let outcomes = race(2, {
            let table = table.clone();
            move |worker| {
                (0..SLOTS)
                    .map(|entry_index| {
                        let start = VirtAddr::from(BASE + entry_index * LARGE);
                        if worker == 0 {
                            (
                                Some(
                                    split_at!(table, start + PAGE, SMALL_LEVEL, true)
                                        .map(discharge),
                                ),
                                None,
                            )
                        } else {
                            let (entry, flush) =
                                table.unmap(common::page_4k(start + 2 * PAGE), true).unwrap();
                            discharge(flush);
                            (None, entry.map(|_| SMALL_LEVEL))
                        }
                    })
                    .collect::<Vec<_>>()
            }
        });
        for (entry_index, (split, unmap)) in outcomes[0].iter().zip(&outcomes[1]).enumerate() {
            let split = split.0.unwrap();
            let removed = unmap.1;
            assert_eq!(removed, Some(SMALL_LEVEL));
            assert_eq!(split, Ok(()));
            for page in [0, 1, 2, 3, 511] {
                let offset = entry_index * LARGE + page * PAGE;
                let expected = if page == 2 {
                    Err(PagingError::NotMapped)
                } else {
                    Ok(PhysAddr::from(frame + offset))
                };
                assert_eq!(table.phys_addr(VirtAddr::from(BASE + offset)), expected);
            }
        }
        assert!(arena.freed().is_empty());
        assert_eq!(table.validate_page_table(), Ok(()));
        locks.assert_balanced();
    }
}

#[test]
fn shared_and_encrypted_updates_split_only_the_selected_huge_leaf() {
    let (arena, table, locks) = fixture(1);
    let table = Arc::new(table);
    let frame = arena.base();
    for entry_index in 0..3 {
        table
            .map(
                common::page_2m(VirtAddr::from(BASE + entry_index * LARGE)),
                common::frame_2m(PhysAddr::from(frame + entry_index * LARGE)),
                flags(),
                false,
            )
            .unwrap();
    }
    race(2, {
        let table = table.clone();
        move |worker| {
            let address = VirtAddr::from(BASE + worker * LARGE + PAGE);
            if worker == 0 {
                discharge(table.set_shared(common::page_4k(address), true).unwrap());
            } else {
                discharge(table.set_private(common::page_4k(address), true).unwrap());
            }
        }
    });
    for page in 0..1024 {
        let address = VirtAddr::from(BASE + page * PAGE);
        assert_eq!(table.walk(address).level(), SMALL_LEVEL);
        assert_eq!(
            table.walk(address).read().raw(),
            leaf_word(frame + page * PAGE, flags(), SMALL_LEVEL)
        );
    }
    let untouched = table.walk(VirtAddr::from(BASE + 2 * LARGE));
    assert_eq!(untouched.level(), LARGE_LEVEL);
    assert_eq!(untouched.read().raw(), leaf_word(frame + 2 * LARGE, flags(), LARGE_LEVEL));
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn splitting_preserves_confidentiality_tags_and_retagging_changes_only_one_leaf() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct EncryptedHost;

    // SAFETY: bit 51 is reserved for the synthetic tag; these tables never run in hardware.
    unsafe impl paging::X86PagingParams for EncryptedHost {
        fn private_mask() -> usize {
            1 << 51
        }

        fn supported_flags() -> paging::PTEntryFlags {
            paging::PTEntryFlags::all()
        }

        fn flush_tlb_global_sync(_scope: FlushScope) {}
    }

    let arena = Arena::new(ARENA);
    let locks = Locks::new(arena.base()..arena.base() + arena.len(), 7);
    let table = PageTable::<X86Paging<EncryptedHost>, Allocator, Lvl<3>, Locks>::new(
        locks.clone(),
        flags(),
    )
    .unwrap();
    let frame = PhysAddr::from(2 * HUGE);
    for shared in [false, true] {
        let base = VirtAddr::from(BASE + usize::from(shared) * LARGE);
        table.map(common::page_2m(base), common::frame_2m(frame), flags(), shared).unwrap();
        let flush = split_at!(table, base, SMALL_LEVEL, true).unwrap();
        // SAFETY: the encryption bit is simulated; these tables never run in hardware.
        unsafe { flush.ignore() };
        for page in 0..512 {
            let address = base + page * PAGE;
            let expected = if shared { 0 } else { 1 << 51 };
            assert_eq!(table.walk(address).read().raw() & (1 << 51), expected);
            assert_eq!(table.phys_addr(address), Ok(frame + page * PAGE));
        }
        let flush = if shared {
            table.set_private(common::page_4k(base + PAGE), true)
        } else {
            table.set_shared(common::page_4k(base + PAGE), true)
        }
        .unwrap();
        // SAFETY: as above; no TLB can cache these mappings.
        unsafe { flush.ignore() };
        for page in 0..512 {
            let private = if page == 1 { shared } else { !shared };
            let expected = if private { 1 << 51 } else { 0 };
            assert_eq!(table.walk(base + page * PAGE).read().raw() & (1 << 51), expected);
            assert_eq!(table.phys_addr(base + page * PAGE), Ok(frame + page * PAGE));
        }
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn last_address_unmaps_and_splits_produce_nonwrapping_flush_scopes() {
    for level in [SMALL_LEVEL, LARGE_LEVEL, HUGE_LEVEL] {
        let (_arena, table, locks) = fixture(1);
        let start = VirtAddr::from(usize::MAX & !(level.size() - 1));
        let last_page = VirtAddr::from(usize::MAX & !(PAGE - 1));
        let frame = PhysAddr::from(2 * HUGE);
        map_at!(table, start, frame, level, flags(), false).unwrap();
        let (entry, flush) = unmap_at!(table, start, level).unwrap();
        assert_eq!(entry.unwrap().raw(), leaf_word(frame.bits(), flags(), level));
        assert_eq!(flush.scope().as_ref().map(|token| token.scope()), Some(FlushScope::All));
        discharge(flush);
        map_at!(table, start, frame, level, flags(), false).unwrap();
        assert_eq!(table.phys_addr(VirtAddr::from(usize::MAX)), Ok(frame + (level.size() - 1)));
        let (entry, flush) = table.unmap(common::page_4k(last_page), true).unwrap();
        assert!(entry.is_some());
        assert_eq!(flush.scope().as_ref().map(|token| token.scope()), Some(FlushScope::All));
        discharge(flush);
        assert_eq!(table.phys_addr(VirtAddr::from(usize::MAX)), Err(PagingError::NotMapped));
        if level != SMALL_LEVEL {
            let previous = last_page - PAGE;
            let (entry, flush) = table.unmap(common::page_4k(previous), true).unwrap();
            assert!(entry.is_some());
            assert_eq!(
                flush.scope().as_ref().map(|token| token.scope()),
                Some(FlushScope::Range { start: previous, end: last_page, level: SMALL_LEVEL })
            );
            discharge(flush);
        }
        assert_eq!(table.validate_page_table(), Ok(()));
        locks.assert_balanced();
    }
}

#[test]
fn typed_4k_unmaps_use_the_page_aligned_flush_scope() {
    let cases = [
        (
            BASE,
            FlushScope::Range {
                start: VirtAddr::from(BASE),
                end: VirtAddr::from(BASE + PAGE),
                level: SMALL_LEVEL,
            },
        ),
        ((1usize << 47) - PAGE, FlushScope::All),
        (usize::MAX & !(PAGE - 1), FlushScope::All),
    ];
    for (start, expected) in cases {
        let (_arena, table, locks) = fixture(1);
        let start = VirtAddr::from(start);
        table
            .map(common::page_4k(start), common::frame_4k(PhysAddr::from(2 * HUGE)), flags(), false)
            .unwrap();
        let (entry, flush) = table.unmap(common::page_4k(start), true).unwrap();
        assert!(entry.is_some());
        assert_eq!(flush.scope().as_ref().map(|token| token.scope()), Some(expected));
        discharge(flush);
        locks.assert_balanced();
    }
}

#[test]
fn reclamation_waits_for_external_readers_and_frees_every_table_once() {
    let (arena, table, locks) = fixture(7);
    let root = table.root_paddr();
    let protected = Arc::new(RwLock::new(Some(table)));
    let (ready, is_ready) = mpsc::channel();
    let (release, released) = mpsc::channel();
    let reader = spawn({
        let protected = protected.clone();
        let arena = arena.clone();
        move || {
            let shared = protected.read().unwrap();
            let table = shared.as_ref().unwrap();
            let vaddr = VirtAddr::from(BASE);
            table
                .map(
                    common::page_4k(vaddr),
                    common::frame_4k(PhysAddr::from(arena.base())),
                    flags(),
                    false,
                )
                .unwrap();
            let snapshot = table.walk(vaddr);
            discharge(table.unmap(common::page_4k(vaddr), true).unwrap().1);
            assert!(snapshot.read().present());
            assert!(table.walk(vaddr).read().is_clear());
            ready.send(()).unwrap();
            released.recv_timeout(WAIT).expect("reader was not released");
            assert!(arena.freed().is_empty());
        }
    });
    is_ready.recv_timeout(WAIT).expect("reader did not acquire the external guard");
    let (blocked, is_blocked) = mpsc::channel();
    let writer = spawn({
        let protected = protected.clone();
        let arena = arena.clone();
        move || {
            assert!(matches!(protected.try_write(), Err(TryLockError::WouldBlock)));
            blocked.send(()).unwrap();
            let mut exclusive = protected.write().unwrap();
            let table = exclusive.as_mut().unwrap();
            // SAFETY: the write guard excludes software walks; Host has no hardware walkers.
            let freed = unsafe { table.free_page_table_by_addr(VirtAddr::from(BASE)) };
            assert_eq!(freed, 3);
            assert_freed_once(&arena, freed);
            assert!(!arena.freed().contains(&root.bits()));
            assert_eq!(table.validate_page_table(), Ok(()));
            // SAFETY: the write guard also excludes every user of the remaining children.
            unsafe { table.free_children() };
            assert_freed_once(&arena, arena.allocated() - 1);
            assert!(!arena.freed().contains(&root.bits()));
            // SAFETY: the already empty tree remains exclusively held.
            unsafe { table.free_children() };
            assert_freed_once(&arena, arena.allocated() - 1);
            drop(exclusive.take());
            assert_freed_once(&arena, arena.allocated());
        }
    });
    is_blocked.recv_timeout(WAIT).expect("writer did not observe the pinned reader");
    assert!(arena.freed().is_empty());
    release.send(()).unwrap();
    finish(reader);
    finish(writer);
    assert!(protected.read().unwrap().is_none());
    assert_eq!(arena.freed().iter().filter(|page| **page == root.bits()).count(), 1);
    locks.assert_balanced();
}

#[test]
fn range_reclamation_respects_siblings_huge_leaves_and_exclusive_end_boundaries() {
    for boundary in [BASE + LARGE, BASE + HUGE] {
        let (arena, table, locks) = fixture(7);
        let protected = RwLock::new(Some(table));
        let start = VirtAddr::from(boundary - PAGE);
        let end = VirtAddr::from(boundary + LARGE);
        let sibling = start - PAGE;
        let huge = end + LARGE;
        {
            let shared = protected.read().unwrap();
            let table = shared.as_ref().unwrap();
            for address in [start, sibling, VirtAddr::from(boundary), end] {
                table
                    .map(
                        common::page_4k(address),
                        common::frame_4k(PhysAddr::from(arena.base())),
                        flags(),
                        false,
                    )
                    .unwrap();
            }
            table
                .map(
                    common::page_2m(huge),
                    common::frame_2m(PhysAddr::from(2 * HUGE)),
                    flags(),
                    false,
                )
                .unwrap();
            for address in [start, VirtAddr::from(boundary), end] {
                let (entry, flush) = table.unmap(common::page_4k(address), true).unwrap();
                assert!(entry.is_some());
                discharge(flush);
            }
            assert!(arena.freed().is_empty());
        }
        let mut exclusive = protected.write().unwrap();
        let table = exclusive.as_mut().unwrap();
        // SAFETY: all software access is excluded and these tables never run in hardware.
        unsafe { table.free_page_table_by_range(start, start) };
        assert!(arena.freed().is_empty());
        // SAFETY: the same exclusive guard covers this half-open range.
        unsafe { table.free_page_table_by_range(start, end) };
        assert_freed_once(&arena, 1);
        assert_eq!(table.phys_addr(sibling), Ok(PhysAddr::from(arena.base())));
        assert_eq!(table.phys_addr(huge + PAGE), Ok(PhysAddr::from(2 * HUGE + PAGE)));
        // SAFETY: the exclusive end was unmapped, but must not have been swept.
        assert_eq!(unsafe { table.free_page_table_by_addr(end) }, 1);
        assert_freed_once(&arena, 2);
        // SAFETY: the sibling is still mapped and must retain its table.
        assert_eq!(unsafe { table.free_page_table_by_addr(start) }, 0);
        discharge(table.unmap(common::page_4k(sibling), true).unwrap().1);
        let left_tables = if boundary == BASE + HUGE { 2 } else { 1 };
        // SAFETY: the last sibling was unmapped under this guard.
        assert_eq!(unsafe { table.free_page_table_by_addr(start) }, left_tables);
        assert_freed_once(&arena, 2 + left_tables);
        // SAFETY: a mapped huge leaf must never be treated as a table page.
        unsafe { table.free_page_table_by_range(huge, huge + LARGE) };
        assert_freed_once(&arena, 2 + left_tables);
        discharge(table.unmap(common::page_2m(huge), true).unwrap().1);
        // SAFETY: the huge leaf is now absent and its flush discharged.
        assert_eq!(unsafe { table.free_page_table_by_addr(huge) }, 2);
        assert_freed_once(&arena, 4 + left_tables);
        assert_eq!(table.validate_page_table(), Ok(()));
        // SAFETY: the remaining direct-map subtree is exclusively owned.
        unsafe { table.free_children() };
        drop(exclusive.take());
        assert_freed_once(&arena, arena.allocated());
        locks.assert_balanced();
    }
}

#[test]
fn five_level_range_cleanup_crosses_the_canonical_gap_without_wrapping() {
    let worker = spawn(|| {
        let arena = Arena::new(ARENA);
        let locks = Locks::new(arena.base()..arena.base() + arena.len(), 1);
        let table =
            PageTable::<X86Paging<Host>, Allocator, Lvl<4>, Locks>::new(locks.clone(), flags())
                .unwrap();
        let root = table.root_paddr();
        let protected = RwLock::new(Some(table));
        let start = VirtAddr::from(0x1000usize);
        let high = VirtAddr::from(0xffff_8000_0000_0000usize);
        let end = high + PAGE;
        let frame = PhysAddr::from(arena.base());
        {
            let shared = protected.read().unwrap();
            let table = shared.as_ref().unwrap();
            for address in [start, high, end] {
                table
                    .map(common::page_4k(address), common::frame_4k(frame), flags(), false)
                    .unwrap();
            }
            for address in [start, high] {
                let (entry, flush) = table.unmap(common::page_4k(address), true).unwrap();
                assert!(entry.is_some());
                discharge(flush);
            }
            assert!(arena.freed().is_empty());
        }
        let mut exclusive = protected.write().unwrap();
        let table = exclusive.as_mut().unwrap();
        // SAFETY: the write guard excludes software users, and Host never installs these tables.
        unsafe { table.free_page_table_by_range(start, end) };
        assert_freed_once(&arena, 3);
        assert!(!arena.freed().contains(&root.bits()));
        assert_eq!(table.phys_addr(end), Ok(frame), "the exclusive end must remain mapped");
        assert_eq!(table.phys_addr(start), Err(PagingError::NotMapped));
        assert_eq!(table.phys_addr(high), Err(PagingError::NotMapped));
        assert_eq!(table.validate_page_table(), Ok(()));
        discharge(table.unmap(common::page_4k(end), true).unwrap().1);
        // SAFETY: the final high-half leaf was unmapped under the same write guard.
        assert_eq!(unsafe { table.free_page_table_by_addr(end) }, 4);
        assert_freed_once(&arena, 7);
        // SAFETY: the remaining direct-map children belong exclusively to this inactive tree.
        unsafe { table.free_children() };
        drop(exclusive.take());
        assert_freed_once(&arena, arena.allocated());
        locks.assert_balanced();
    });
    finish(worker);
}

struct BudgetAllocator;
static ALLOCATION_BUDGET: AtomicUsize = AtomicUsize::new(usize::MAX);

// SAFETY: allocation and the direct map are the fixture's; only failure timing changes.
unsafe impl DirectMappedAllocator for BudgetAllocator {
    fn direct_map() -> (Range<PhysAddr>, VirtAddr) {
        Allocator::direct_map()
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        ALLOCATION_BUDGET
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |left| left.checked_sub(1))
            .map_err(|_| PagingError::AllocFrame)?;
        <Allocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(page: PhysAddr) {
        // SAFETY: ownership is forwarded unchanged to the original allocator.
        unsafe { <Allocator as DirectMappedAllocator>::deallocate_table_page(page) };
    }
}

type BudgetTable = PageTable<X86Paging<Host>, BudgetAllocator, Lvl<3>, Locks>;

#[test]
fn construction_failures_return_all_allocated_pages_without_locking_content() {
    for budget in 0..3 {
        let arena = Arena::new(ARENA);
        let locks = Locks::new(arena.base()..arena.base() + arena.len(), 1);
        ALLOCATION_BUDGET.store(budget, Ordering::Relaxed);
        let result = BudgetTable::new(locks.clone(), flags()).map(drop);
        assert_eq!(result, Err(PagingError::AllocFrame));
        assert_eq!(arena.allocated(), budget);
        assert_freed_once(&arena, budget);
        assert_eq!(locks.0.calls.load(Ordering::Relaxed), 0);
        assert_eq!(locks.0.unlocks.load(Ordering::Relaxed), 0);
    }
}

#[test]
fn constructor_self_mapping_checks_reject_absent_leaves_and_reclaim_the_tree() {
    let arena = Arena::new(ARENA);
    let locks = Locks::new(arena.base()..arena.base() + arena.len(), 1);
    let absent = flags() & !PTEntryFlags::PRESENT;
    let result = Table::new(locks.clone(), absent).map(drop);
    assert_eq!(result, Err(PagingError::TablePageNotSelfMapped));
    assert_eq!(arena.allocated(), 3);
    assert_freed_once(&arena, arena.allocated());
    assert_eq!(locks.0.calls.load(Ordering::Relaxed), 0);
}

#[test]
fn failed_growth_and_split_leave_retryable_mappings_and_release_content_guards() {
    let arena = Arena::new(ARENA);
    ALLOCATION_BUDGET.store(3, Ordering::Relaxed);
    let locks = Locks::new(arena.base()..arena.base() + arena.len(), 1);
    let table = BudgetTable::new(locks.clone(), flags()).unwrap();
    let vaddr = VirtAddr::from(BASE);
    let frame = PhysAddr::from(arena.base());
    let original = table.walk(vaddr);
    let before = arena.allocated();
    ALLOCATION_BUDGET.store(1, Ordering::Relaxed);
    assert_eq!(
        table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false),
        Err(PagingError::AllocFrame)
    );
    assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
    assert_eq!(table.walk(vaddr).level(), original.level());
    assert_eq!(table.walk(vaddr).read().raw(), original.read().raw());
    assert_eq!(arena.allocated(), before + 1);
    assert_freed_once(&arena, 1);
    assert_eq!(locks.0.calls.load(Ordering::Relaxed), 0);
    assert_eq!(locks.0.unlocks.load(Ordering::Relaxed), 0);
    ALLOCATION_BUDGET.store(3, Ordering::Relaxed);
    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    let huge = VirtAddr::from(BASE + HUGE);
    map_at!(table, huge, PhysAddr::from(2 * HUGE), HUGE_LEVEL, flags(), false).unwrap();
    let old = table.walk(huge + PAGE).read().raw();
    let before = arena.allocated();
    ALLOCATION_BUDGET.store(1, Ordering::Relaxed);
    assert!(matches!(
        split_at!(table, huge + PAGE, SMALL_LEVEL, true),
        Err(PagingError::AllocFrame)
    ));
    assert_eq!(arena.allocated(), before + 1);
    assert_freed_once(&arena, 2);
    assert_eq!(table.walk(huge + PAGE).read().raw(), old);
    assert_eq!(table.walk(huge + PAGE).level(), HUGE_LEVEL);
    assert_eq!(table.phys_addr(huge + PAGE), Ok(PhysAddr::from(2 * HUGE + PAGE)));
    locks.assert_balanced();
    ALLOCATION_BUDGET.store(2, Ordering::Relaxed);
    discharge(split_at!(table, huge + PAGE, SMALL_LEVEL, true).unwrap());
    assert_eq!(table.walk(huge + PAGE).level(), SMALL_LEVEL);
    assert_eq!(table.phys_addr(huge + PAGE), Ok(PhysAddr::from(2 * HUGE + PAGE)));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

#[test]
fn constructor_covers_unaligned_direct_maps_without_content_locks() {
    let arena = Arena::new(ARENA);
    let physical_base = 0x2000_1000;
    arena.rebase(physical_base);
    let locks = Locks::new(physical_base..physical_base + arena.len(), 1);
    let table =
        PageTable::<X86Paging<Host>, RebasedAllocator, Lvl<3>, Locks>::new(locks.clone(), flags())
            .unwrap();
    for offset in (0..ARENA).step_by(PAGE) {
        let address = VirtAddr::from(arena.base() + offset);
        let expected = PhysAddr::from(physical_base + offset);
        assert_eq!(table.phys_addr(address), Ok(expected));
        assert_eq!(table.translate(address).unwrap().level(), SMALL_LEVEL);
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(locks.0.calls.load(Ordering::Relaxed), 0);
    assert_eq!(locks.0.unlocks.load(Ordering::Relaxed), 0);
}

#[test]
fn content_lock_keys_are_physical_even_with_a_nonidentity_direct_map() {
    let arena = Arena::new(ARENA);
    let physical_base = 0x2000_0000;
    arena.rebase(physical_base);
    let locks = Locks::new(physical_base..physical_base + arena.len(), 7);
    let table = Arc::new(
        PageTable::<X86Paging<Host>, RebasedAllocator, Lvl<3>, Locks>::new(locks.clone(), flags())
            .unwrap(),
    );
    assert_eq!(table.root_paddr(), PhysAddr::from(physical_base));
    assert_eq!(
        <RebasedAllocator as paging::os_contract::PagingAllocator>::paddr_to_vaddr(
            table.root_paddr()
        ),
        VirtAddr::from(arena.base())
    );
    race(8, {
        let table = table.clone();
        move |worker| {
            let address = VirtAddr::from(BASE + worker * PAGE);
            table
                .map(
                    common::page_4k(address),
                    common::frame_4k(PhysAddr::from(physical_base + worker * PAGE)),
                    flags(),
                    false,
                )
                .unwrap();
        }
    });
    for worker in 0..8 {
        assert_eq!(
            table.phys_addr(VirtAddr::from(BASE + worker * PAGE)),
            Ok(PhysAddr::from(physical_base + worker * PAGE))
        );
    }
    let keys = locks.0.keys.lock().unwrap();
    assert!(keys.contains(&physical_base));
    assert!(keys.iter().all(|key| *key < physical_base + arena.allocated() * PAGE));
    drop(keys);
    assert_eq!(table.validate_page_table(), Ok(()));
    locks.assert_balanced();
}

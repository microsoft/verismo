//! Ensures competing mutations do not lose mappings or corrupt shared-path growth and split updates.
mod common;

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{mpsc, Arc, Barrier};
use std::thread;
use std::time::Duration;

use common::{flags, Table};
use paging::{
    address::{PhysAddr, VirtAddr},
    arch::x86_64::PTEntryFlags,
    structs::{PageLevel, PagingError},
};

const BASE: usize = 0x4000_0000;
const PAGE: usize = 4096;

fn race<T: Send + 'static>(job: impl Fn(usize) -> T + Send + Sync + 'static) -> Vec<T> {
    let start = Arc::new(Barrier::new(5));
    let job = Arc::new(job);
    let (send, receive) = mpsc::channel();
    let workers: Vec<_> = (0..4)
        .map(|index| {
            let start = start.clone();
            let job = job.clone();
            let send = send.clone();
            thread::spawn(move || {
                start.wait();
                send.send((index, catch_unwind(AssertUnwindSafe(|| job(index)))))
                    .expect("race receiver remains live");
            })
        })
        .collect();
    start.wait();
    let mut results: Vec<_> = (0..4)
        .map(|_| receive.recv_timeout(Duration::from_secs(10)).expect("mutation timed out"))
        .collect();
    for worker in workers {
        worker.join().unwrap();
    }
    results.sort_by_key(|(index, _)| *index);
    results
        .into_iter()
        .map(|(_, result)| result.unwrap_or_else(|panic| resume_unwind(panic)))
        .collect()
}

#[test]
fn competing_maps_and_unmaps_have_one_winner() {
    let (arena, table) = common::table();
    let table = Arc::new(table);
    let base = arena.base();
    let results = race({
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
    let winner = results.iter().position(Result::is_ok).unwrap();
    assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
    for (index, result) in results.iter().enumerate() {
        if index != winner {
            assert_eq!(*result, Err(PagingError::EntryAlreadyPresent { level: PageLevel::Level0 }));
        }
    }
    assert_eq!(table.phys_addr(VirtAddr::from(BASE)), Ok(PhysAddr::from(base + winner * PAGE)));
    let expected = table.walk(VirtAddr::from(BASE)).read().raw();
    let removed = race({
        let table = table.clone();
        move |_| {
            let (entry, flush) =
                table.unmap(common::page_4k(VirtAddr::from(BASE)), Some(true)).unwrap();
            // SAFETY: these host-backed tables are never installed in hardware.
            unsafe { flush.ignore() };
            entry.map(|entry| entry.raw())
        }
    });
    assert_eq!(removed.into_iter().flatten().collect::<Vec<_>>(), vec![expected]);
    assert_eq!(table.phys_addr(VirtAddr::from(BASE)), Err(PagingError::NotMapped));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn disjoint_maps_preserve_shared_path_growth() {
    let (arena, table) = common::table();
    let table = Arc::new(table);
    let frame = PhysAddr::from(arena.base());
    race({
        let table = table.clone();
        move |index| {
            table
                .map(
                    common::page_4k(VirtAddr::from(BASE + index * PAGE)),
                    common::frame_4k(frame + index * PAGE),
                    flags(),
                    false,
                )
                .unwrap();
        }
    });
    for index in 0..4 {
        assert_eq!(table.phys_addr(VirtAddr::from(BASE + index * PAGE)), Ok(frame + index * PAGE));
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn concurrent_subpage_updates_preserve_neighbors_after_splitting() {
    let (arena, table): (_, Table) = common::table();
    let frame = PhysAddr::from(arena.base());
    table
        .map(common::page_2m(VirtAddr::from(BASE)), common::frame_2m(frame), flags(), false)
        .unwrap();
    let table = Arc::new(table);
    let readonly = flags() & !PTEntryFlags::WRITABLE;
    race({
        let table = table.clone();
        move |index| {
            let flush = table
                .set_flags(common::page_4k(VirtAddr::from(BASE + index * PAGE)), readonly, true)
                .unwrap();
            // SAFETY: these host-backed tables are never installed in hardware.
            unsafe { flush.ignore() };
        }
    });
    for index in 0..4 {
        let address = VirtAddr::from(BASE + index * PAGE);
        assert_eq!(table.phys_addr(address), Ok(frame + index * PAGE));
        assert!(!table.walk(address).read().writable());
    }
    assert!(table.walk(VirtAddr::from(BASE + 4 * PAGE)).read().writable());
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

//! Stateless allocators leave external root ownership entirely with the caller.
#![cfg(feature = "use_ad")]

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

use common::Host;
use paging::address::{PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::PageLevel;
use paging::mapping::{MappingMut, MappingMutOps};
use paging::{PTEntryFlags, X86Paging};

#[cfg(feature = "use_ad")]
#[test]
fn staged_commit_preserves_late_accessed_dirty_bits() {
    type Arch = X86Paging<Host>;

    let initial = PTEntry::<Arch>::new(
        PhysAddr::from(0x4000usize),
        PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE,
    );
    let word = AtomicUsize::new(initial.raw());
    let entry = (&word as *const AtomicUsize).cast_mut().cast::<PTEntry<Arch>>();
    // SAFETY: `word` has the entry's transparent layout and is accessed atomically.
    let mut mapping =
        unsafe { MappingMut::new(Some(VirtAddr::from(0x8000usize)), PageLevel::Level0, entry) };
    mapping
        .staged()
        .entry
        .set(PhysAddr::from(0x4000usize), PTEntryFlags::PRESENT | PTEntryFlags::NX);

    let hardware_ad = (PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY).bits();
    word.fetch_or(hardware_ad, Ordering::AcqRel);
    let pending = mapping.commit();
    // SAFETY: this host-only entry is never installed in a hardware page table.
    unsafe { pending.ignore() };

    let committed = PTEntryFlags::from_bits_retain(word.load(Ordering::Acquire));
    assert!(committed.contains(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
    assert!(committed.contains(PTEntryFlags::PRESENT | PTEntryFlags::NX));
    assert!(!committed.contains(PTEntryFlags::WRITABLE));
}

#[cfg(feature = "use_ad")]
#[test]
#[should_panic(expected = "present leaf/table transitions require architecture-aware publication")]
fn staged_commit_rejects_present_leaf_table_transition() {
    type Arch = X86Paging<Host>;

    let initial = PTEntry::<Arch>::new(
        PhysAddr::from(0x20_0000usize),
        PTEntryFlags::PRESENT | PTEntryFlags::HUGE,
    );
    let word = AtomicUsize::new(initial.raw());
    let entry = (&word as *const AtomicUsize).cast_mut().cast::<PTEntry<Arch>>();
    // SAFETY: `word` has the entry's transparent layout and is accessed atomically.
    let mut mapping =
        unsafe { MappingMut::new(Some(VirtAddr::from(0x20_0000usize)), PageLevel::Level1, entry) };
    *mapping.staged().entry =
        PTEntry::new_table(PhysAddr::from(0x40_0000usize), PTEntryFlags::PRESENT);
    let _ = mapping.commit();
}

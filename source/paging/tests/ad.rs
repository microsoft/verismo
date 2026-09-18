mod common;

use std::collections::BTreeSet;
#[cfg(feature = "concurrent")]
use std::mem::ManuallyDrop;
use std::mem::{align_of, size_of};
use std::sync::Arc;

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{load_entry, published_bits, Allocator, Arena, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::{LevelSpec, Lvl, PageLevel};
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::ptpage::PTPage;
use paging::sizes::{entry_index, PT_ENTRY_COUNT};
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Platform;

unsafe impl X86PagingParams for Platform {
    fn private_mask() -> usize {
        1 << 51
    }

    fn shared_mask() -> usize {
        1 << 50
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_: FlushScope) {}
}

type Arch = X86Paging<Platform>;
type Entry = PTEntry<Arch>;
type Page = PTPage<Arch, Allocator>;
#[cfg(feature = "concurrent")]
type Table<L> = PageTable<Arch, Allocator, L, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type Table<L> = PageTable<Arch, Allocator, L>;
const AD: usize = 0x60;
const PAGE: usize = 4096;
const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x8000_0000;

#[test]
fn constructor_and_flag_edits_normalize_publication() {
    assert_eq!(size_of::<Entry>(), size_of::<usize>());
    assert_eq!(align_of::<Entry>(), align_of::<usize>());
    assert_eq!(size_of::<Page>(), PAGE);
    assert_eq!(align_of::<Page>(), PAGE);
    for bits in [0, 0x20, 0x40, 0x400, 1, 3, 0x21, 0x41, 0x61, 0x80, 0x81] {
        let flags = PTEntryFlags::from_bits_retain(bits);
        let address = PhysAddr::from(FRAME);
        assert_eq!(Entry::new(address, flags).raw(), published_bits(FRAME | bits));
        let mut entry = Entry::new(address, flags);
        entry.clear_flags(PTEntryFlags::from_bits_retain(bits));
        entry.set_flags(flags);
        assert_eq!(entry.raw(), published_bits(FRAME | bits));
    }
}

unsafe fn tree_words(root: PhysAddr, level: PageLevel) -> Vec<(usize, usize, PageLevel)> {
    let mut words = Vec::new();
    for index in 0..PT_ENTRY_COUNT {
        let pte = Page::entry_ptr(root.bits() as *const Page, index);
        // SAFETY: the caller pins this well-formed, identity-mapped tree without reclamation.
        let entry = unsafe { load_entry(pte) };
        words.push((pte as usize, entry.raw(), level));
        if entry.is_table(level) {
            words.extend(unsafe {
                tree_words(PhysAddr::from(entry.address()), level.child().unwrap())
            });
        }
    }
    words
}

unsafe fn assert_path_history(root: PhysAddr, address: VirtAddr, mut level: PageLevel) {
    let mut page = root;
    loop {
        let pte = Page::entry_ptr(page.bits() as *const Page, entry_index(address, level));
        // SAFETY: the caller pins the quiesced path, whose table addresses are identity-mapped.
        let entry = unsafe { load_entry(pte) };
        assert!(entry.present());
        assert_eq!(entry.raw() & AD, published_bits(1) & AD);
        if !entry.is_table(level) {
            break;
        }
        page = PhysAddr::from(entry.address());
        level = level.child().unwrap();
    }
}

unsafe fn clear_history_before_import(
    root: PhysAddr,
    level: PageLevel,
) -> Vec<(usize, usize, PageLevel)> {
    // SAFETY: all controllers and hardware users of these pages are quiesced by the caller.
    let words = unsafe { tree_words(root, level) };
    for &(pte, word, _) in &words {
        if word & 1 != 0 {
            unsafe { (pte as *mut usize).write(word & !AD) };
        }
    }
    let &(absent, _, _) = words.iter().find(|(_, word, _)| *word == 0).unwrap();
    unsafe { (absent as *mut usize).write(0xdead_0020) };
    unsafe { tree_words(root, level) }
}

fn assert_words(words: &[(usize, usize, PageLevel)], expected: impl Fn(usize) -> usize) {
    assert!(words.iter().any(|(_, word, _)| *word == 0xdead_0020));
    for &(pte, before, _) in words {
        // SAFETY: the imported controller retains these initialized, atomically accessed entries.
        let after = unsafe { load_entry(pte as *const Entry) }.raw();
        assert_eq!(after, expected(before), "entry {pte:#x}");
    }
}

fn assert_all_reclaimed(arena: &Arena) {
    let freed = arena.freed();
    assert_eq!(freed.len(), arena.allocated());
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), freed.len());
}

fn fixture<L: LevelSpec>() -> (Arc<Arena>, Table<L>) {
    let arena = Arena::new(ARENA);
    #[cfg(feature = "concurrent")]
    let table = Table::new(WholeTreeLock::default(), common::flags()).unwrap();
    #[cfg(not(feature = "concurrent"))]
    let table = Table::new(common::flags()).unwrap();
    (arena, table)
}

unsafe fn adopt<L: LevelSpec>(root: PhysAddr) -> Result<Table<L>, PagingError> {
    #[cfg(feature = "concurrent")]
    return unsafe { Table::from_root(WholeTreeLock::default(), root) };
    #[cfg(not(feature = "concurrent"))]
    unsafe {
        Table::from_root(root)
    }
}

macro_rules! ad_tests {
    ($module:ident, $fixture:ident, $adopt:ident) => {
        #[allow(unused_mut)]
        mod $module {
            use super::*;

            #[test]
            fn parent_leaf_protection_split_and_encryption_preserve_the_selected_ad_mode() {
                for split in [false, true] {
                    let (arena, mut table) = $fixture::<Lvl<3>>();
                    let base = VirtAddr::from(BASE);
                    let address = base + PAGE;
                    let requested = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE;
                    let parent = requested | PTEntryFlags::USER;
                    let (mapped, frame, level) = if split {
                        (base, FRAME, PageLevel::Level1)
                    } else {
                        (address, FRAME + PAGE, PageLevel::Level0)
                    };
                    map_at_with_parent_flags!(
                        table,
                        mapped,
                        PhysAddr::from(frame),
                        level,
                        requested,
                        false,
                        parent
                    )
                    .unwrap();
                    // SAFETY: the newly constructed path remains exclusively owned and inactive.
                    unsafe { assert_path_history(table.root_paddr(), address, PageLevel::Level3) };
                    if split {
                        let pending = split_at!(table, address, PageLevel::Level0, true).unwrap();
                        // SAFETY: these host tables are never installed or cached by hardware.
                        unsafe { pending.ignore() };
                    }
                    assert_eq!(table.walk(address).read().raw() & AD, published_bits(1) & AD);
                    let readonly = PTEntryFlags::PRESENT | PTEntryFlags::NX;
                    let pending =
                        set_flags_at!(table, address, PageLevel::Level0, readonly, true).unwrap();
                    unsafe { pending.ignore() };
                    for shared in [true, false] {
                        let pending = if shared {
                            table.set_shared(common::page_4k(address), true)
                        } else {
                            table.set_private(common::page_4k(address), true)
                        }
                        .unwrap();
                        unsafe { pending.ignore() };
                        let entry = table.walk(address).read();
                        assert_eq!(entry.raw() & AD, published_bits(1) & AD);
                        assert!(!entry.writable());
                        assert_eq!(entry.is_shared(), shared);
                        assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(FRAME + PAGE)));
                    }
                    // SAFETY: the table stays owned and has no hardware or concurrent users.
                    for (_, word, _) in unsafe { tree_words(table.root_paddr(), PageLevel::Level3) }
                    {
                        if !cfg!(feature = "use_ad") && word & 1 != 0 {
                            assert_eq!(word & AD, AD);
                        }
                    }
                    let (_, pending) = table.unmap(common::page_4k(address), true).unwrap();
                    unsafe { pending.ignore() };
                    assert_eq!(table.walk(address).read().raw(), 0);
                    drop(table);
                    assert_all_reclaimed(&arena);
                }
            }

            #[test]
            fn imported_four_and_five_level_trees_normalize_only_present_entries() {
                fn check<L: LevelSpec>() {
                    let (arena, mut original) = fixture::<L>();
                    let address = VirtAddr::from(BASE);
                    original
                        .map(
                            common::page_4k(address),
                            common::frame_4k(PhysAddr::from(FRAME)),
                            common::flags(),
                            false,
                        )
                        .unwrap();
                    #[cfg(feature = "concurrent")]
                    let (_locks, root) = original.leak();
                    #[cfg(not(feature = "concurrent"))]
                    let root = original.leak();
                    // SAFETY: this leaked tree has no controllers or hardware users.
                    let before = unsafe { clear_history_before_import(root, L::LEVEL) };
                    // SAFETY: ownership transfers; no hardware runs, so no cache invalidation is needed.
                    let imported = unsafe { $adopt::<L>(root) }.unwrap();
                    assert_words(&before, published_bits);
                    assert_eq!(imported.phys_addr(address), Ok(PhysAddr::from(FRAME)));
                    assert_eq!(imported.validate_page_table(), Ok(()));
                    drop(imported);
                    assert_all_reclaimed(&arena);
                }
                check::<Lvl<3>>();
                check::<Lvl<4>>();
            }

            #[test]
            fn populate_normalizes_new_subtrees_but_not_rejected_or_identical_attachments() {
                let (arena, mut table) = $fixture::<Lvl<3>>();
                let address = VirtAddr::from(BASE);
                let index = entry_index(address, PageLevel::Level3);
                assert_eq!(table.next_table_pa(index), None);
                let (upper, upper_pa) = Page::alloc().unwrap();
                let (middle, middle_pa) = Page::alloc().unwrap();
                let (leaf, leaf_pa) = Page::alloc().unwrap();
                // SAFETY: these three freshly allocated pages are private and exclusively owned.
                unsafe {
                    Page::entry_ptr_mut(upper, entry_index(address, PageLevel::Level2))
                        .write(Entry::new(middle_pa, PTEntryFlags::PRESENT));
                    Page::entry_ptr_mut(middle, entry_index(address, PageLevel::Level1))
                        .write(Entry::new(leaf_pa, PTEntryFlags::PRESENT));
                    Page::entry_ptr_mut(leaf, entry_index(address, PageLevel::Level0))
                        .cast::<usize>()
                        .write(FRAME | 1);
                }
                let before = unsafe { clear_history_before_import(upper_pa, PageLevel::Level2) };
                // SAFETY: ownership transfers; all pages and hardware users are quiesced.
                assert_eq!(unsafe { table.populate(index, upper_pa) }, Ok(true));
                assert_words(&before, published_bits);
                assert_eq!(table.phys_addr(address), Ok(PhysAddr::from(FRAME)));

                // SAFETY: the attached subtree remains quiesced while raw import state is staged.
                let before = unsafe { clear_history_before_import(upper_pa, PageLevel::Level2) };
                assert_eq!(unsafe { table.populate(index, upper_pa) }, Ok(false));
                assert_words(&before, core::convert::identity);

                let (rejected, rejected_pa) = Page::alloc().unwrap();
                // SAFETY: the candidate is a private level-two table with one huge data mapping.
                unsafe {
                    Page::entry_ptr_mut(rejected, 0).cast::<usize>().write(FRAME | 0x81);
                }
                let rejected_before =
                    unsafe { clear_history_before_import(rejected_pa, PageLevel::Level2) };
                assert!(unsafe { table.populate(index, rejected_pa) }.is_err());
                assert_words(&rejected_before, core::convert::identity);
                assert_words(&before, core::convert::identity);
                assert_eq!(table.next_table_pa(index), Some(upper_pa));
                assert!(arena.freed().is_empty());
                // SAFETY: rejection retains this unlinked candidate, which has no child tables.
                unsafe { Allocator::deallocate_table_page(rejected_pa) };
                drop(table);
                assert_all_reclaimed(&arena);
            }

            #[test]
            fn rejected_imports_do_not_normalize_or_free_the_caller_owned_root() {
                let arena = Arena::new(ARENA);
                let (page, root) = Page::alloc().unwrap();
                let absent = entry_index(VirtAddr::from(root.bits()), PageLevel::Level0);
                let present = (absent + 1) % PT_ENTRY_COUNT;
                // SAFETY: this newly allocated root is private and all accesses are quiesced.
                unsafe {
                    Page::entry_ptr_mut(page, absent).cast::<usize>().write(0xdead_0020);
                    Page::entry_ptr_mut(page, present).cast::<usize>().write(FRAME | 1);
                }
                let result = unsafe { $adopt::<Lvl<0>>(root) };
                assert!(matches!(result, Err(PagingError::TablePageNotSelfMapped)));
                assert_eq!(unsafe { load_entry(Page::entry_ptr(page, absent)) }.raw(), 0xdead_0020);
                assert_eq!(unsafe { load_entry(Page::entry_ptr(page, present)) }.raw(), FRAME | 1);
                assert!(arena.freed().is_empty());
                // SAFETY: rejection left this unlinked root under the original allocator's ownership.
                unsafe { Allocator::deallocate_table_page(root) };
                assert_all_reclaimed(&arena);
            }
        }
    };
}

ad_tests!(selected_controller, fixture, adopt);

#[cfg(feature = "concurrent")]
#[test]
fn borrowed_import_normalizes_shared_descendants_only_while_all_controllers_are_quiesced() {
    let arena = Arena::new(ARENA);
    let locks = WholeTreeLock::default();
    let kernel = Table::<Lvl<3>>::new(locks.clone(), common::flags()).unwrap();
    kernel
        .map(
            common::page_4k(VirtAddr::from(BASE)),
            common::frame_4k(PhysAddr::from(FRAME)),
            common::flags(),
            false,
        )
        .unwrap();
    // SAFETY: the inactive roots share all prefixes in the same lock domain.
    let user = unsafe { Table::new_from_sharing_top::<0, 512>(locks.clone(), &kernel) }.unwrap();
    let root = user.root_paddr();
    // SAFETY: both original controllers are unused until normalization finishes; no hardware ran.
    let before = unsafe { clear_history_before_import(root, PageLevel::Level3) };
    let imported = ManuallyDrop::new(unsafe { Table::<Lvl<3>>::from_root(locks, root) }.unwrap());
    assert_words(&before, published_bits);
    assert_eq!(kernel.phys_addr(VirtAddr::from(BASE)), Ok(PhysAddr::from(FRAME)));
    drop(ManuallyDrop::into_inner(imported).leak());
    assert!(arena.freed().is_empty());
    drop(user);
    drop(kernel);
    assert_all_reclaimed(&arena);
}

extern crate alloc;

use alloc::rc::Rc;
use core::cell::{Cell, UnsafeCell};
use core::mem::{align_of, size_of};
use core::ops::Deref;
#[cfg(any(feature = "use_ad", feature = "concurrent"))]
use core::sync::atomic::AtomicUsize;

use super::*;
use crate::structs::level::{LevelSpec, Lvl};
use crate::structs::policy::KernelPolicy;
use crate::structs::ptpage::{free_children, reclaim_path, reclaim_range};
use crate::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

impl<A: ArchPagingMeta, P: PagingAllocator> PTPagePointer<'_, A, P> {
    fn is_empty(&self) -> bool {
        self.entries_satisfy(&|entry| !entry.present())
    }
}

fn test_page<A: ArchPagingMeta, P: PagingAllocator>(entry: PTEntry<A>) -> PTPage<A, P> {
    PTPage {
        #[cfg(any(feature = "use_ad", feature = "concurrent"))]
        entries: core::array::from_fn(|_| AtomicUsize::new(entry.raw())),
        #[cfg(not(any(feature = "use_ad", feature = "concurrent")))]
        entries: [entry; ENTRY_COUNT],
        dummy: PhantomData,
    }
}

fn published(word: usize) -> usize {
    if !cfg!(feature = "use_ad") && word & 1 != 0 {
        word | 0x60
    } else {
        word
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Host;

unsafe impl X86PagingParams for Host {
    fn private_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_: FlushScope) {}
}

#[derive(Clone)]
struct NoAllocator;

// SAFETY: live addresses are identity-mapped; allocation is unsupported.
unsafe impl PagingAllocator for NoAllocator {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        VirtAddr::from(paddr.bits())
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        PhysAddr::from(vaddr.bits())
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        Err(PagingError::AllocFrame)
    }

    unsafe fn deallocate_table_page(&self, _: PhysAddr) {
        panic!("no frame belongs to this allocator");
    }
}

type Arch = X86Paging<Host>;
type Page = PTPage<Arch, NoAllocator>;
type View<'tree> = PTPagePointer<'tree, Arch, NoAllocator>;
type Entry = PTEntry<Arch>;

struct Owner {
    allocator: NoAllocator,
    memory: UnsafeCell<Page>,
}

impl Owner {
    fn new() -> Self {
        Self { allocator: NoAllocator, memory: UnsafeCell::new(test_page(Entry::empty())) }
    }

    fn view(&self) -> View<'_> {
        // SAFETY: this borrow pins initialized storage; shared entry accesses are atomic.
        unsafe {
            View::from_root(
                &self.allocator,
                PhysAddr::from(self.memory.get() as usize),
                PageLevel::Level0,
            )
        }
    }
}

#[test]
fn owned_tree_with_zero_sized_allocator_stores_only_root_and_level() {
    assert_eq!(size_of::<PTPageTree<Arch, NoAllocator>>(), size_of::<(PhysAddr, PageLevel)>());
}

#[test]
fn typed_roots_and_controllers_store_no_runtime_level_or_duplicate_allocator() {
    fn check<L: LevelSpec>() {
        assert_eq!(size_of::<PTPageTree<Arch, NoAllocator, L>>(), size_of::<PhysAddr>());
        assert_eq!(
            size_of::<PTPageTree<TreeArch, AllocationOwner, L>>(),
            size_of::<(AllocationOwner, PhysAddr)>()
        );
        #[cfg(not(feature = "concurrent"))]
        assert_eq!(
            size_of::<crate::pagetable::PageTable<TreeArch, AllocationOwner, L>>(),
            size_of::<(AllocationOwner, PhysAddr)>()
        );
        #[cfg(feature = "concurrent")]
        assert_eq!(
            size_of::<crate::pagetable::PageTable<TreeArch, AllocationOwner, L, ()>>(),
            size_of::<(AllocationOwner, PhysAddr)>()
        );
    }
    check::<Lvl<0>>();
    check::<Lvl<1>>();
    check::<Lvl<2>>();
    check::<Lvl<3>>();
    check::<Lvl<4>>();
    assert_eq!(size_of::<AllocationTree>(), size_of::<(AllocationOwner, PhysAddr, PageLevel)>());
}

#[test]
fn exclusive_private_entry_edits_preserve_layout_and_live_atomic_access() {
    let mut page: Page = test_page(Entry::empty());
    let base = &mut page as *mut Page as usize;
    let last = page.entry_mut(ENTRY_COUNT - 1) as *mut Entry as usize;
    assert_eq!(base % 4096, 0);
    assert_eq!(last - base, (ENTRY_COUNT - 1) * size_of::<Entry>());
    page.entry_mut(0).set(PhysAddr::from(0x1000usize), crate::PTEntryFlags::PRESENT);
    *page.entry_mut(ENTRY_COUNT - 1) = Entry::from_bits(0xdead_0020);
    assert_eq!(page.entry_mut(0).raw(), published(0x1001));
    assert_eq!(page.entry_mut(ENTRY_COUNT - 1).raw(), 0xdead_0020);
    let owner = Owner { allocator: NoAllocator, memory: UnsafeCell::new(page) };
    let view = owner.view();
    assert_eq!(view.load(0).raw(), published(0x1001));
    assert_eq!(view.load(ENTRY_COUNT - 1).raw(), 0xdead_0020);
    view.store(0, Entry::empty());
    assert!(view.is_empty());
    assert_eq!(view.load(ENTRY_COUNT - 1).raw(), 0xdead_0020);
}

#[test]
fn views_access_both_page_boundaries_and_return_snapshots() {
    let owner = Owner::new();
    let view = owner.view();
    assert!(view.is_empty());
    view.store(0, Entry::from_bits(0x1001));
    view.store(ENTRY_COUNT - 1, Entry::from_bits(0x2001));
    let snapshot = view.load(0);
    assert!(!view.is_empty());
    assert_eq!(view.swap(0, Entry::from_bits(0x3001)).raw(), published(0x1001));
    assert_eq!(snapshot.raw(), published(0x1001));
    assert_eq!(view.load(0).raw(), published(0x3001));
    assert_eq!(view.load(ENTRY_COUNT - 1).raw(), published(0x2001));
    for index in 1..ENTRY_COUNT - 1 {
        assert_eq!(view.load(index).raw(), 0);
    }
    view.store(0, Entry::empty());
    view.store(ENTRY_COUNT - 1, Entry::empty());
    assert!(view.is_empty());
    assert_eq!(view.level(), PageLevel::Level0);
    assert_eq!(view.paddr().bits(), owner.memory.get() as usize);
    assert!(matches!(view.allocator(), NoAllocator));
    assert_eq!(size_of::<View<'_>>(), 4 * size_of::<usize>());
    assert_eq!(size_of::<Page>(), 4096);
    assert_eq!(align_of::<Page>(), 4096);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TaggedHost;

unsafe impl X86PagingParams for TaggedHost {
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

type TreeArch = X86Paging<TaggedHost>;
type TreeEntry = PTEntry<TreeArch>;
type TreePage = PTPage<TreeArch, TreeOwner>;
type TreeView<'tree> = PTPagePointer<'tree, TreeArch, TreeOwner>;

type AllocationPage = PTPage<TreeArch, AllocationOwner>;
type AllocationTree = PTPageTree<TreeArch, AllocationOwner>;
type AllocationView<'tree> = PTPagePointer<'tree, TreeArch, AllocationOwner>;

#[derive(Clone)]
struct AllocationOwner(Rc<AllocationState>);

struct AllocationState {
    pages: [UnsafeCell<AllocationPage>; 8],
    allocated: Cell<usize>,
    budget: Cell<usize>,
    freed: Cell<usize>,
}

impl Deref for AllocationOwner {
    type Target = AllocationState;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AllocationOwner {
    fn new() -> Self {
        Self(Rc::new(AllocationState {
            pages: core::array::from_fn(|_| {
                UnsafeCell::new(test_page(TreeEntry::from_bits(usize::MAX)))
            }),
            allocated: Cell::new(0),
            budget: Cell::new(8),
            freed: Cell::new(0),
        }))
    }

    fn page_index(&self, paddr: PhysAddr) -> usize {
        assert_eq!(paddr.bits() & 4095, 0);
        let index = (paddr.bits() / 4096).checked_sub(1).expect("invalid table frame");
        assert!(index < self.allocated.get(), "resolved a data frame or uncleared tag");
        assert_eq!(self.freed.get() & (1 << index), 0, "resolved a freed table");
        index
    }

    fn view<'tree>(
        &'tree self,
        tree: &'tree AllocationTree,
        level: PageLevel,
    ) -> AllocationView<'tree> {
        // SAFETY: the owner and tree borrows pin the initialized, unpublished pages.
        unsafe { AllocationView::from_root(self, tree.root_paddr(), level) }
    }
}

// SAFETY: clones share allocation state and pin the same distinct aligned page storage.
unsafe impl PagingAllocator for AllocationOwner {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        VirtAddr::from(self.pages[self.page_index(paddr)].get() as usize)
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        let index = self
            .pages
            .iter()
            .position(|page| page.get() as usize == vaddr.bits())
            .expect("address outside this owner");
        let paddr = PhysAddr::from((index + 1) * 4096);
        self.page_index(paddr);
        paddr
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        let index = self.allocated.get();
        if self.budget.get() == 0 || index == self.pages.len() {
            return Err(PagingError::AllocFrame);
        }
        self.budget.set(self.budget.get() - 1);
        self.allocated.set(index + 1);
        Ok(PhysAddr::from((index + 1) * 4096))
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        let index = self.page_index(paddr);
        for (page_index, page) in self.pages.iter().take(self.allocated.get()).enumerate() {
            if self.freed.get() & (1 << page_index) != 0 {
                continue;
            }
            for slot in 0..ENTRY_COUNT {
                // SAFETY: this fixture retains all initialized arena storage without concurrent access.
                let entry = unsafe { AllocationPage::read_entry(page.get(), slot) };
                assert!(
                    !entry.present() || entry.address() != paddr.bits(),
                    "freed a table while a parent still links to it"
                );
            }
        }
        self.freed.set(self.freed.get() | (1 << index));
    }
}

#[test]
fn cloned_allocators_share_allocations_resolutions_and_deallocation() {
    let owner = AllocationOwner::new();
    let clone = owner.clone();
    let (_, first) = AllocationPage::alloc(&owner).unwrap();
    let (_, second) = AllocationPage::alloc(&clone).unwrap();
    assert_ne!(first, second);
    assert_eq!(owner.allocated.get(), 2);
    assert_eq!(clone.allocated.get(), 2);
    for frame in [first, second] {
        let address = owner.paddr_to_vaddr(frame);
        assert_eq!(clone.paddr_to_vaddr(frame), address);
        assert_eq!(clone.vaddr_to_paddr(address), frame);
    }
    // SAFETY: both frames are unlinked and both clones share the allocation domain.
    unsafe {
        clone.deallocate_table_page(first);
        owner.deallocate_table_page(second);
    }
    assert_eq!(owner.freed.get(), 0b11);
    assert_eq!(clone.freed.get(), 0b11);
}

#[test]
fn owned_tree_keeps_allocator_state_alive_after_the_original_handle_drops() {
    let owner = AllocationOwner::new();
    let state = Rc::downgrade(&owner.0);
    let mut tree = AllocationTree::new(owner.clone(), PageLevel::Level2).unwrap();
    drop(owner);
    assert_eq!(state.strong_count(), 1);
    tree.grow(
        VirtAddr::from(0usize),
        PageLevel::Level0,
        <TreeArch as ArchPagingMeta>::PTFlags::parent_flags(),
    )
    .unwrap();
    assert_eq!(state.strong_count(), 1);
    let observer = AllocationOwner(state.upgrade().expect("tree retains its allocator"));
    assert_eq!(observer.allocated.get(), 3);
    assert_eq!(
        observer.view(&tree, PageLevel::Level2).walk(VirtAddr::from(0usize)).page.level(),
        PageLevel::Level0
    );
    drop(tree);
    assert_eq!(observer.freed.get(), 0b111);
    assert_eq!(state.strong_count(), 1);
    drop(observer);
    assert!(state.upgrade().is_none());
}

#[test]
fn owned_tree_allocates_and_zeroes_its_root_at_every_level() {
    for level in [
        PageLevel::Level0,
        PageLevel::Level1,
        PageLevel::Level2,
        PageLevel::Level3,
        PageLevel::Level4,
    ] {
        let owner = AllocationOwner::new();
        let tree = AllocationTree::new(owner.clone(), level).unwrap();
        assert_eq!(tree.root_paddr().bits(), 0x1000);
        assert_eq!(owner.allocated.get(), 1);
        assert_eq!(owner.paddr_to_vaddr(tree.root_paddr()).bits() & 4095, 0);
        let view = owner.view(&tree, level);
        assert_eq!(view.walk(VirtAddr::from(0usize)).page.level(), level);
        for index in 0..ENTRY_COUNT {
            assert_eq!(view.load(index).raw(), 0);
        }
        drop(tree);
        assert_eq!(owner.freed.get(), 1);
    }
}

#[test]
fn owned_tree_reports_root_allocation_failure_without_freeing() {
    let owner = AllocationOwner::new();
    owner.budget.set(0);
    assert!(matches!(
        AllocationTree::new(owner.clone(), PageLevel::Level2),
        Err(PagingError::AllocFrame)
    ));
    assert_eq!(owner.allocated.get(), 0);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(Rc::strong_count(&owner.0), 1);
}

#[test]
fn typed_roots_allocate_at_the_static_level_and_transfer_all_parts_without_freeing() {
    fn check<L: LevelSpec>() {
        let owner = AllocationOwner::new();
        let tree = PTPageTree::<TreeArch, _, L>::new_root(owner.clone(), KernelPolicy).unwrap();
        let root = tree.root_paddr();
        assert_eq!(root.bits(), 0x1000);
        assert!(Rc::ptr_eq(&tree.allocator.0, &owner.0));
        assert!(matches!(tree.policy(), KernelPolicy));
        {
            let view = tree.root();
            assert_eq!(view.level(), L::LEVEL);
            assert_eq!(view.paddr(), root);
            assert!(view.is_empty());
            assert!(Rc::ptr_eq(&view.allocator().0, &owner.0));
            assert_eq!(Rc::strong_count(&owner.0), 2);
        }
        assert_eq!(Rc::strong_count(&owner.0), 2);
        let (allocator, policy, released) = tree.into_parts();
        assert_eq!(released, root);
        assert!(matches!(policy, KernelPolicy));
        assert!(Rc::ptr_eq(&allocator.0, &owner.0));
        assert_eq!(Rc::strong_count(&owner.0), 2);
        assert_eq!(owner.freed.get(), 0);
        // SAFETY: into_parts transferred this initialized, inactive root at L::LEVEL.
        let adopted =
            unsafe { PTPageTree::<TreeArch, _, L>::from_root(allocator, released, policy) };
        assert_eq!(adopted.root().level(), L::LEVEL);
        drop(adopted);
        assert_eq!(owner.freed.get(), 1);
        assert_eq!(Rc::strong_count(&owner.0), 1);
    }
    check::<Lvl<0>>();
    check::<Lvl<1>>();
    check::<Lvl<2>>();
    check::<Lvl<3>>();
    check::<Lvl<4>>();
}

#[test]
fn typed_root_allocation_failure_retains_no_allocator_or_frames() {
    let owner = AllocationOwner::new();
    owner.budget.set(0);
    assert!(matches!(
        PTPageTree::<TreeArch, _, Lvl<4>>::new_root(owner.clone(), KernelPolicy),
        Err(PagingError::AllocFrame)
    ));
    assert_eq!(owner.allocated.get(), 0);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(Rc::strong_count(&owner.0), 1);
}

#[test]
fn typed_adoption_recursively_drops_dynamically_prepared_trees() {
    fn check<L: LevelSpec>() {
        let owner = AllocationOwner::new();
        let mut prepared = AllocationTree::new(owner.clone(), L::LEVEL).unwrap();
        let address = VirtAddr::from(0usize);
        prepared
            .grow(address, PageLevel::Level0, <TreeArch as ArchPagingMeta>::PTFlags::parent_flags())
            .unwrap();
        prepared.root().walk(address).entry().store(TreeEntry::from_bits(0xdead_0001));
        let root = prepared.release();
        assert_eq!(owner.allocated.get(), L::DEPTH + 1);
        assert_eq!(owner.freed.get(), 0);
        assert_eq!(Rc::strong_count(&owner.0), 1);
        // SAFETY: release transferred an exclusively owned tree built at L::LEVEL.
        let tree =
            unsafe { PTPageTree::<TreeArch, _, L>::from_root(owner.clone(), root, KernelPolicy) };
        assert_eq!(tree.root().walk(address).entry().load().raw(), published(0xdead_0001));
        drop(tree);
        assert_eq!(owner.freed.get(), (1 << owner.allocated.get()) - 1);
        assert_eq!(Rc::strong_count(&owner.0), 1);
    }
    check::<Lvl<3>>();
    check::<Lvl<4>>();
}

#[test]
fn owned_tree_grows_downward_reuses_paths_and_drops_tables_not_data() {
    let owner = AllocationOwner::new();
    let mut tree = AllocationTree::new(owner.clone(), PageLevel::Level3).unwrap();
    let root = tree.root_paddr();
    let flags = <TreeArch as ArchPagingMeta>::PTFlags::parent_flags();
    let address = VirtAddr::from(
        2 * PageLevel::Level3.size()
            + 3 * PageLevel::Level2.size()
            + 4 * PageLevel::Level1.size()
            + 5 * PageLevel::Level0.size(),
    );
    tree.grow(address, PageLevel::Level1, flags).unwrap();
    assert_eq!(Rc::strong_count(&owner.0), 2);
    assert_eq!(owner.allocated.get(), 3);
    {
        let view = owner.view(&tree, PageLevel::Level3);
        assert_eq!(view.walk(address).page.level(), PageLevel::Level1);
        let middle = view.child(2).ok().expect("level-two table");
        let leaf = middle.child(3).ok().expect("level-one table");
        assert_eq!(middle.level(), PageLevel::Level2);
        assert_eq!(leaf.level(), PageLevel::Level1);
        assert_eq!(
            view.load(2).raw(),
            TreeEntry::new_table(TreeArch::make_private_address(middle.paddr()), flags).raw()
        );
        assert_eq!(
            middle.load(3).raw(),
            TreeEntry::new_table(TreeArch::make_private_address(leaf.paddr()), flags).raw()
        );
        assert!(leaf.entries_satisfy(&|entry| entry.is_clear()));
    }
    tree.grow(address, PageLevel::Level1, flags).unwrap();
    tree.grow(address, PageLevel::Level2, flags).unwrap();
    assert_eq!(owner.allocated.get(), 3);
    tree.grow(address, PageLevel::Level0, flags).unwrap();
    assert_eq!(owner.allocated.get(), 4);
    tree.grow(address + PageLevel::Level1.size(), PageLevel::Level0, flags).unwrap();
    assert_eq!(Rc::strong_count(&owner.0), 2);
    assert_eq!(owner.allocated.get(), 5);
    assert_eq!(tree.root_paddr(), root);
    {
        let view = owner.view(&tree, PageLevel::Level3);
        let leaf = view.walk(address);
        assert_eq!(leaf.page.level(), PageLevel::Level0);
        assert!(leaf.entry().load().is_clear());
        leaf.entry().store(TreeEntry::from_bits(0xdead_0001));
        let middle = view.child(2).ok().unwrap().child(3).ok().unwrap();
        middle.store(6, TreeEntry::from_bits(0x20_0081));
        middle.store(7, TreeEntry::from_bits(0xd080));
    }
    tree.grow(address, PageLevel::Level0, flags).unwrap();
    assert_eq!(owner.allocated.get(), 5);
    assert_eq!(owner.freed.get(), 0);
    drop(tree);
    assert_eq!(owner.freed.get(), 0b1_1111);
    assert_eq!(Rc::strong_count(&owner.0), 1);
}

#[test]
fn owned_tree_release_transfers_all_pages_without_freeing() {
    let owner = AllocationOwner::new();
    let root = {
        let mut tree = AllocationTree::new(owner.clone(), PageLevel::Level2).unwrap();
        tree.grow(
            VirtAddr::from(0usize),
            PageLevel::Level0,
            <TreeArch as ArchPagingMeta>::PTFlags::parent_flags(),
        )
        .unwrap();
        assert_eq!(Rc::strong_count(&owner.0), 2);
        let expected = tree.root_paddr();
        let released = tree.release();
        assert_eq!(Rc::strong_count(&owner.0), 1);
        assert_eq!(released, expected);
        released
    };
    assert_eq!(owner.allocated.get(), 3);
    assert_eq!(owner.freed.get(), 0);
    // SAFETY: release transferred this unpublished subtree to the test.
    unsafe { AllocationPage::free_unpublished(&owner, root, PageLevel::Level2) };
    assert_eq!(owner.freed.get(), 0b111);
}

#[test]
fn owned_tree_failed_growth_rolls_back_only_the_staged_suffix() {
    for budget in 0..3 {
        let owner = AllocationOwner::new();
        let mut tree = AllocationTree::new(owner.clone(), PageLevel::Level4).unwrap();
        let flags = <TreeArch as ArchPagingMeta>::PTFlags::parent_flags();
        let address = VirtAddr::from(PageLevel::Level3.size());
        tree.grow(address, PageLevel::Level3, flags).unwrap();
        let root = tree.root_paddr();
        let snapshots = {
            let view = owner.view(&tree, PageLevel::Level4);
            let child = view.child(0).ok().unwrap();
            child.store(1, TreeEntry::from_bits(0xd080));
            child.store(2, TreeEntry::from_bits(0xe000));
            [
                core::array::from_fn::<_, ENTRY_COUNT, _>(|index| view.load(index).raw()),
                core::array::from_fn::<_, ENTRY_COUNT, _>(|index| child.load(index).raw()),
            ]
        };
        owner.budget.set(budget);
        assert!(matches!(
            tree.grow(address, PageLevel::Level0, flags),
            Err(PagingError::AllocFrame)
        ));
        assert_eq!(Rc::strong_count(&owner.0), 2);
        assert_eq!(tree.root_paddr(), root);
        assert_eq!(owner.allocated.get(), 2 + budget);
        assert_eq!(owner.freed.get(), ((1 << budget) - 1) << 2);
        {
            let view = owner.view(&tree, PageLevel::Level4);
            let child = view.child(0).ok().unwrap();
            for (index, (&root_entry, &child_entry)) in
                snapshots[0].iter().zip(&snapshots[1]).enumerate()
            {
                assert_eq!(view.load(index).raw(), root_entry);
                assert_eq!(child.load(index).raw(), child_entry);
            }
            assert_eq!(view.walk(address).page.level(), PageLevel::Level3);
        }
        owner.budget.set(3);
        tree.grow(address, PageLevel::Level0, flags).unwrap();
        assert_eq!(Rc::strong_count(&owner.0), 2);
        assert_eq!(
            owner.view(&tree, PageLevel::Level4).walk(address).page.level(),
            PageLevel::Level0
        );
        drop(tree);
        assert_eq!(owner.freed.get(), (1 << owner.allocated.get()) - 1);
        assert_eq!(Rc::strong_count(&owner.0), 1);
    }
}

#[test]
fn owned_tree_rejects_upward_growth_and_blocking_huge_leaves() {
    let owner = AllocationOwner::new();
    let mut tree = AllocationTree::new(owner.clone(), PageLevel::Level2).unwrap();
    let flags = <TreeArch as ArchPagingMeta>::PTFlags::parent_flags();
    let address = VirtAddr::from(0usize);
    assert!(matches!(tree.grow(address, PageLevel::Level3, flags), Err(PagingError::InvalidLevel)));
    assert!(owner.view(&tree, PageLevel::Level2).entries_satisfy(&|entry| entry.is_clear()));
    owner.view(&tree, PageLevel::Level2).store(0, TreeEntry::from_bits(0x8000_0081));
    assert!(matches!(tree.grow(address, PageLevel::Level0, flags), Err(PagingError::NotLeafEntry)));
    tree.grow(address, PageLevel::Level2, flags).unwrap();
    assert_eq!(owner.view(&tree, PageLevel::Level2).load(0).raw(), published(0x8000_0081));
    assert_eq!(owner.allocated.get(), 1);
    assert_eq!(owner.freed.get(), 0);
    drop(tree);
    assert_eq!(owner.freed.get(), 1);
}

#[derive(Clone)]
struct TreeOwner(Rc<TreeState>);

struct TreeState {
    pages: [UnsafeCell<TreePage>; 5],
    allocated: Cell<usize>,
    resolutions: Cell<usize>,
    inverse_resolutions: Cell<usize>,
    freed: Cell<usize>,
    freed_order: Cell<usize>,
    require_clear_on_free: Cell<bool>,
}

impl Deref for TreeOwner {
    type Target = TreeState;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TreeOwner {
    fn new() -> Self {
        let owner = Self(Rc::new(TreeState {
            pages: core::array::from_fn(|_| UnsafeCell::new(test_page(TreeEntry::empty()))),
            allocated: Cell::new(0),
            resolutions: Cell::new(0),
            inverse_resolutions: Cell::new(0),
            freed: Cell::new(0),
            freed_order: Cell::new(0),
            require_clear_on_free: Cell::new(true),
        }));
        for expected in [0x1000usize, 0x2000, 0x3000, 0x4000, 0x5000] {
            assert_eq!(owner.allocate_table_page().unwrap().bits(), expected);
        }
        let table = <TreeArch as ArchPagingMeta>::PTFlags::parent_flags();
        // SAFETY: the fixture still exclusively owns these unpublished pages.
        unsafe {
            TreePage::entry_ptr_mut(owner.pages[0].get(), 0).write(TreeEntry::new_table(
                TreeArch::make_private_address(PhysAddr::from(0x2000usize)),
                table,
            ));
            TreePage::entry_ptr_mut(owner.pages[0].get(), 1)
                .write(TreeEntry::from_bits(0x8000_0081));
            TreePage::entry_ptr_mut(owner.pages[0].get(), 2).write(TreeEntry::from_bits(0xd080));
            TreePage::entry_ptr_mut(owner.pages[1].get(), 7).write(TreeEntry::new_table(
                TreeArch::make_shared_address(PhysAddr::from(0x3000usize)),
                table,
            ));
            TreePage::entry_ptr_mut(owner.pages[1].get(), 8).write(TreeEntry::from_bits(0x20_0081));
            TreePage::entry_ptr_mut(owner.pages[2].get(), 9).write(TreeEntry::from_bits(0xd081));
        }
        owner
    }

    fn view(&self) -> TreeView<'_> {
        // SAFETY: borrowing the owner pins every initialized page and its resolver.
        unsafe { TreeView::from_root(self, PhysAddr::from(0x1000usize), PageLevel::Level2) }
    }

    fn page_index(&self, paddr: PhysAddr) -> usize {
        assert_eq!(paddr.bits() & 4095, 0);
        let index = (paddr.bits() / 4096).checked_sub(1).expect("invalid table frame");
        assert!(index < self.allocated.get(), "resolved a data frame or uncleared tag");
        assert_eq!(self.freed.get() & (1 << index), 0, "resolved a freed table");
        index
    }
}

// SAFETY: clones share allocation state and pin the same distinct aligned page storage.
unsafe impl PagingAllocator for TreeOwner {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        let index = self.page_index(paddr);
        self.resolutions.set(self.resolutions.get() + 1);
        VirtAddr::from(self.pages[index].get() as usize)
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        self.inverse_resolutions.set(self.inverse_resolutions.get() + 1);
        let index = self
            .pages
            .iter()
            .position(|page| page.get() as usize == vaddr.bits())
            .expect("address outside this owner");
        PhysAddr::from((index + 1) * 4096)
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        let index = self.allocated.get();
        if index == self.pages.len() {
            return Err(PagingError::AllocFrame);
        }
        self.allocated.set(index + 1);
        Ok(PhysAddr::from((index + 1) * 4096))
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        let index = self.page_index(paddr);
        assert_ne!(index, 0, "free_children must retain the root");
        for (page_index, page) in self.pages.iter().enumerate() {
            let level = [
                PageLevel::Level2,
                PageLevel::Level1,
                PageLevel::Level0,
                PageLevel::Level3,
                PageLevel::Level4,
            ][page_index];
            for slot in 0..ENTRY_COUNT {
                // SAFETY: this quiesced fixture retains the backing storage of its arena.
                let entry = unsafe { TreePage::read_entry(page.get(), slot) };
                assert!(!entry.is_table(level) || entry.address() != paddr.bits());
                if page_index == index && self.require_clear_on_free.get() {
                    assert!(entry.is_clear());
                }
            }
        }
        self.freed.set(self.freed.get() | (1 << index));
        self.freed_order.set(self.freed_order.get() * 16 + index + 1);
    }
}

#[test]
fn child_views_inherit_the_resolver_and_derive_clean_physical_identity_and_level() {
    let owner = TreeOwner::new();
    let root = owner.view();
    let middle = root.child(0).ok().expect("root table link");
    let leaf = middle.child(7).ok().expect("middle table link");
    assert_eq!(root.level(), PageLevel::Level2);
    assert_eq!(middle.level(), PageLevel::Level1);
    assert_eq!(leaf.level(), PageLevel::Level0);
    assert_eq!(root.paddr().bits(), 0x1000);
    assert_eq!(middle.paddr().bits(), 0x2000);
    assert_eq!(leaf.paddr().bits(), 0x3000);
    assert!(Rc::ptr_eq(&root.allocator().0, &owner.0));
    assert!(Rc::ptr_eq(&root.allocator().0, &middle.allocator().0));
    assert!(Rc::ptr_eq(&middle.allocator().0, &leaf.allocator().0));
    assert_eq!(owner.resolutions.get(), 3);
    assert_eq!(leaf.load(9).raw(), 0xd081);
    assert_ne!(owner.pages[2].get() as usize, leaf.paddr().bits());
}

#[test]
fn views_borrow_clone_only_allocators_without_owning_table_frames() {
    let owner = TreeOwner::new();
    assert_eq!(size_of::<TreeView<'_>>(), 4 * size_of::<usize>());
    assert_eq!(size_of::<AllocationView<'_>>(), 4 * size_of::<usize>());
    assert_eq!(Rc::strong_count(&owner.0), 1);
    let root = owner.view();
    assert!(Rc::ptr_eq(&root.allocator().0, &owner.0));
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(owner.resolutions.get(), 1);
    let middle = root.child(0).ok().expect("root table link");
    assert!(Rc::ptr_eq(&middle.allocator().0, &owner.0));
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(owner.resolutions.get(), 2);
    let leaf = middle.child(7).ok().expect("middle table link");
    assert!(Rc::ptr_eq(&leaf.allocator().0, &owner.0));
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(owner.resolutions.get(), 3);
    assert_eq!(owner.inverse_resolutions.get(), 0);
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(leaf.load(9).raw(), 0xd081);
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(owner.allocated.get(), 5);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(owner.resolutions.get(), 3);
    assert_eq!(owner.inverse_resolutions.get(), 0);
}

#[test]
fn walk_retains_the_stopping_node_and_tree_borrow() {
    let owner = TreeOwner::new();
    let address = VirtAddr::from(7 * PageLevel::Level1.size() + 9 * PageLevel::Level0.size());
    let observed = {
        let root = owner.view();
        let observed = root.walk(address);
        assert_eq!(Rc::strong_count(&owner.0), 1);
        assert_eq!(owner.resolutions.get(), 3);
        assert_eq!(owner.inverse_resolutions.get(), 0);
        observed
    };
    assert_eq!(Rc::strong_count(&owner.0), 1);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(observed.page.level(), PageLevel::Level0);
    assert_eq!(observed.entry().load().raw(), 0xd081);
    assert_eq!(observed.index, 9);
    assert!(Rc::ptr_eq(&observed.page.allocator().0, &owner.0));
    assert_eq!(Rc::strong_count(&owner.0), 1);
}

#[test]
fn walk_retains_the_stopping_node_without_inverse_resolution() {
    let owner = TreeOwner::new();
    let root = owner.view();
    assert_eq!(owner.resolutions.get(), 1);
    assert_eq!(owner.inverse_resolutions.get(), 0);
    assert_eq!(root.paddr().bits(), 0x1000);
    let address = VirtAddr::from(7 * PageLevel::Level1.size() + 9 * PageLevel::Level0.size());
    for (address, page_index, level, word) in [
        (VirtAddr::from(PageLevel::Level2.size()), 0, PageLevel::Level2, 0x8000_0081),
        (VirtAddr::from(0usize), 1, PageLevel::Level1, 0),
        (address, 2, PageLevel::Level0, 0xd081),
    ] {
        let inverse = owner.inverse_resolutions.get();
        let observed = root.walk(address);
        assert_eq!(observed.page.level(), level);
        assert_eq!(owner.inverse_resolutions.get(), inverse);
        assert_eq!(observed.page.paddr().bits(), (page_index + 1) * 0x1000);
        assert_eq!(observed.entry().load().raw(), word);
        assert_eq!(observed.index, entry_index(address, level));
    }
    assert_eq!(owner.inverse_resolutions.get(), 4);
}

#[test]
fn walk_supports_every_root_level_and_retains_nonpresent_metadata() {
    for level in [
        PageLevel::Level0,
        PageLevel::Level1,
        PageLevel::Level2,
        PageLevel::Level3,
        PageLevel::Level4,
    ] {
        let owner = Owner::new();
        let paddr = PhysAddr::from(owner.memory.get() as usize);
        // SAFETY: an empty initialized page is a valid root at each tested level.
        let view = unsafe { View::from_root(&owner.allocator, paddr, level) };
        assert_eq!(size_of::<View<'_>>(), 4 * size_of::<usize>());
        assert_eq!(view.level(), level);
        assert_eq!(view.paddr(), paddr);
        view.store(0, Entry::from_bits(0x1000));
        assert!(view.is_empty());
        let observed = view.walk(VirtAddr::from(0usize));
        assert_eq!(observed.page.level(), level);
        let snapshot = observed.entry().load();
        assert_eq!(snapshot.raw(), 0x1000);
        assert_eq!(observed.page.paddr(), paddr);
        assert_eq!(view.swap(0, Entry::empty()).raw(), 0x1000);
        assert_eq!(snapshot.raw(), 0x1000);
        assert_eq!(observed.entry().load().raw(), 0);
        assert!(view.is_empty());
    }
}

#[test]
fn high_roots_walk_through_each_child_level_to_the_leaf() {
    let owner = TreeOwner::new();
    let flags = <TreeArch as ArchPagingMeta>::PTFlags::parent_flags();
    // SAFETY: neither additional root has been published or viewed.
    unsafe {
        TreePage::entry_ptr_mut(owner.pages[3].get(), 0)
            .write(TreeEntry::new_table(PhysAddr::from(0x1000usize), flags));
        TreePage::entry_ptr_mut(owner.pages[4].get(), 0)
            .write(TreeEntry::new_table(PhysAddr::from(0x4000usize), flags));
    }
    // SAFETY: these roots extend the same pinned, initialized fixture tree.
    let root3 =
        unsafe { TreeView::from_root(&owner, PhysAddr::from(0x4000usize), PageLevel::Level3) };
    let root4 =
        unsafe { TreeView::from_root(&owner, PhysAddr::from(0x5000usize), PageLevel::Level4) };
    assert_eq!(root3.level(), PageLevel::Level3);
    assert_eq!(root4.level(), PageLevel::Level4);
    let address = VirtAddr::from(7 * PageLevel::Level1.size() + 9 * PageLevel::Level0.size());
    for observed in [root3.walk(address), root4.walk(address)] {
        assert_eq!(observed.page.level(), PageLevel::Level0);
        assert_eq!(observed.entry().load().raw(), 0xd081);
        assert_eq!(observed.page.paddr().bits(), 0x3000);
    }
    assert_eq!(owner.inverse_resolutions.get(), 2);
}

#[test]
fn child_lookup_never_resolves_huge_absent_or_level_zero_entries() {
    let owner = TreeOwner::new();
    let root = owner.view();
    for (index, expected) in [(1, 0x8000_0081), (2, 0xd080), (3, 0)] {
        assert_eq!(root.child(index).err().expect("stopping entry").raw(), expected);
    }
    assert_eq!(owner.resolutions.get(), 1);
    let middle = root.child(0).ok().expect("root table link");
    assert_eq!(middle.child(8).err().expect("huge leaf").raw(), 0x20_0081);
    let leaf = middle.child(7).ok().expect("middle table link");
    for word in [0xd081, 0xd001] {
        leaf.store(9, TreeEntry::from_bits(word));
        assert_eq!(leaf.child(9).err().expect("level-zero leaf").raw(), published(word));
        assert_eq!(owner.resolutions.get(), 3);
        let observed = leaf.walk(VirtAddr::from(9 * PageLevel::Level0.size()));
        assert_eq!(observed.entry().load().raw(), published(word));
        assert_eq!(observed.page.level(), PageLevel::Level0);
    }
    assert_eq!(owner.resolutions.get(), 3);
}

#[test]
fn a_walk_result_observes_later_publication_and_continues_from_its_node() {
    let owner = TreeOwner::new();
    let root = owner.view();
    let stopped = root.walk(VirtAddr::from(PageLevel::Level2.size()));
    let snapshot = stopped.entry().load();
    let table = root.swap(0, TreeEntry::empty());
    root.store(1, table);
    assert_eq!(snapshot.raw(), 0x8000_0081);
    assert_eq!(stopped.page.level(), PageLevel::Level2);
    assert_eq!(stopped.index, 1);
    assert!(stopped.entry().load().is_table(stopped.page.level()));
    assert_eq!(root.child(1).ok().expect("published table").paddr().bits(), 0x2000);
    let resolutions = owner.resolutions.get();
    let continued = stopped.page.walk(VirtAddr::from(PageLevel::Level2.size()));
    assert_eq!(continued.page.level(), PageLevel::Level1);
    assert!(continued.entry().load().is_clear());
    assert_eq!(owner.resolutions.get(), resolutions + 1);
}

#[test]
fn derived_teardown_unlinks_empty_children_before_freeing_and_retains_data_frames() {
    let owner = TreeOwner::new();
    let root = owner.view();
    // SAFETY: the fixture is exclusively accessed and no child view has escaped.
    unsafe { free_children(&root, |_| true) };
    assert!(root.is_empty());
    for index in 0..ENTRY_COUNT {
        assert!(root.load(index).is_clear());
    }
    assert_eq!(owner.freed.get(), 0b110);
    assert_eq!(owner.freed_order.get(), 0x32);
    assert_eq!(owner.resolutions.get(), 3);
}

#[test]
fn teardown_applies_ownership_only_at_the_supplied_root() {
    let owner = TreeOwner::new();
    let root = owner.view();
    let table = root.load(0).raw();
    // SAFETY: selected slots are exclusively owned, with no installed hardware walks.
    unsafe { free_children(&root, |index| index != 0) };
    assert_eq!(root.load(0).raw(), table);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(owner.resolutions.get(), 1);
    unsafe { free_children(&root, |index| index == 0) };
    assert!(root.is_empty());
    assert_eq!(owner.freed.get(), 0b110);
}

#[test]
fn path_reclamation_distinguishes_absent_metadata_from_clear_words() {
    let owner = TreeOwner::new();
    owner.require_clear_on_free.set(false);
    let root = owner.view();
    {
        let middle = root.child(0).ok().expect("middle table");
        let leaf = middle.child(7).ok().expect("leaf table");
        middle.store(8, TreeEntry::empty());
        leaf.store(9, TreeEntry::from_bits(0xd080));
    }
    let address = VirtAddr::from(7 * PageLevel::Level1.size() + 9 * PageLevel::Level0.size());
    // SAFETY: no child view survives and both predicates reject present mappings.
    assert_eq!(unsafe { reclaim_path(&root, address, |entry| entry.is_clear()) }, 0);
    assert_eq!(owner.freed.get(), 0);
    assert_eq!(unsafe { reclaim_path(&root, address, |entry| !entry.present()) }, 2);
    assert_eq!(owner.freed.get(), 0b110);
    assert!(root.load(0).is_clear());
    assert_eq!(root.load(1).raw(), 0x8000_0081);
}

#[test]
fn range_reclamation_preserves_outside_mappings_and_skipped_root_entries() {
    let owner = TreeOwner::new();
    let root = owner.view();
    {
        let middle = root.child(0).ok().expect("middle table");
        let leaf = middle.child(7).ok().expect("leaf table");
        leaf.store(9, TreeEntry::empty());
    }
    let start = 7 * PageLevel::Level1.size();
    let end = start + PageLevel::Level0.size();
    let calls = Cell::new(0);
    // SAFETY: the local range is valid and all selected descendants are exclusively owned.
    unsafe {
        reclaim_range(
            &root,
            start,
            end,
            |index| {
                calls.set(calls.get() + 1);
                assert_eq!(index, 0);
                false
            },
            |entry| entry.is_clear(),
        )
    };
    assert_eq!(calls.get(), 1);
    assert_eq!(owner.freed.get(), 0);
    unsafe {
        reclaim_range(
            &root,
            start,
            end,
            |index| {
                assert_eq!(index, 0);
                true
            },
            |entry| entry.is_clear(),
        )
    };
    assert_eq!(owner.freed.get(), 0b100);
    {
        let middle = root.child(0).ok().expect("outside mapping retains its table");
        assert!(middle.load(7).is_clear());
        assert_eq!(middle.load(8).raw(), 0x20_0081);
        middle.store(8, TreeEntry::empty());
    }
    unsafe { reclaim_range(&root, start, end, |_| true, |entry| entry.is_clear()) };
    assert_eq!(owner.freed.get(), 0b110);
    assert!(root.load(0).is_clear());
    assert_eq!(root.load(1).raw(), 0x8000_0081);
}

#[test]
fn leaf_root_reclamation_never_frees_or_clears_data_mappings() {
    let owner = Owner::new();
    let root = owner.view();
    root.store(0, Entry::from_bits(0x1081));
    // SAFETY: this root has no descendants and is not installed in hardware.
    assert_eq!(unsafe { reclaim_path(&root, VirtAddr::from(0usize), |entry| !entry.present()) }, 0);
    unsafe {
        reclaim_range(&root, 0, PageLevel::Level0.size(), |_| true, |entry| entry.is_clear())
    };
    assert_eq!(root.load(0).raw(), published(0x1081));
    unsafe { free_children(&root, |_| false) };
    assert_eq!(root.load(0).raw(), published(0x1081));
    unsafe { free_children(&root, |_| true) };
    assert!(root.is_empty());
}

#[test]
#[should_panic(expected = "index <")]
fn child_lookup_checks_bounds_before_reading() {
    let owner = TreeOwner::new();
    let _ = owner.view().child(ENTRY_COUNT);
}

#[test]
fn atomic_publication_presets_only_present_words_and_preserves_exact_observations() {
    use core::sync::atomic::{AtomicUsize, Ordering};

    let word = AtomicUsize::new(0);
    // SAFETY: this local atomic pins the slot; every access uses the same atomic word.
    let slot = unsafe { PTEntryRef::<Arch>::from_raw(word.as_ptr().cast()) };
    let raw =
        |result: Result<Entry, Entry>| result.map(|entry| entry.raw()).map_err(|entry| entry.raw());
    for before in [0, 0x1020, 0x1001, 0x1061] {
        for after in [0, 0x2040, 0x2001, 0x2061] {
            word.store(before, Ordering::Release);
            assert_eq!(slot.load().raw(), before);
            assert_eq!(Entry::from_bits(before).raw(), before);
            slot.store(Entry::from_bits(after));
            assert_eq!(slot.load().raw(), published(after));

            word.store(before, Ordering::Release);
            assert_eq!(slot.swap(Entry::from_bits(after)).raw(), before);
            assert_eq!(slot.load().raw(), published(after));

            word.store(before, Ordering::Release);
            assert_eq!(
                raw(slot
                    .compare_exchange(Entry::from_bits(before ^ 0x1000), Entry::from_bits(after))),
                Err(before)
            );
            assert_eq!(slot.load().raw(), before);
            assert_eq!(
                raw(slot.compare_exchange(Entry::from_bits(before), Entry::from_bits(after))),
                Ok(before)
            );
            assert_eq!(slot.load().raw(), published(after));
        }
        for mask in [usize::MAX, !0x60, !1, 0] {
            word.store(before, Ordering::Release);
            assert_eq!(slot.fetch_and(mask).raw(), before);
            assert_eq!(slot.load().raw(), published(before & mask));
        }
        for mask in [0, 1, 0x60, 0x2000] {
            word.store(before, Ordering::Release);
            assert_eq!(slot.fetch_or(mask).raw(), before);
            assert_eq!(slot.load().raw(), published(before | mask));
        }
    }
}

#[test]
fn compare_exchange_rejects_a_stale_snapshot_without_overwriting_updates() {
    let owner = Owner::new();
    let view = owner.view();
    let current = Entry::from_bits(published(0x1001));
    let updated = Entry::from_bits(published(0x1003));
    let raw =
        |result: Result<Entry, Entry>| result.map(|entry| entry.raw()).map_err(|entry| entry.raw());
    view.store(0, current);
    assert_eq!(raw(view.entry(0).compare_exchange(current, updated)), Ok(current.raw()));
    assert_eq!(raw(view.entry(0).compare_exchange(current, Entry::empty())), Err(updated.raw()));
    assert_eq!(view.load(0).raw(), updated.raw());
    assert_eq!(raw(view.entry(0).compare_exchange(updated, Entry::empty())), Ok(updated.raw()));
}

#[test]
fn invalidation_rollback_retains_the_old_encoding_and_late_history() {
    let owner = Owner::new();
    let slot = owner.view().entry(0);
    let original = Entry::from_bits(published(0x20_0181));
    slot.store(original);
    {
        let invalidated = InvalidatedLeaf::new(slot);
        assert_eq!(slot.load().raw(), original.raw() & !1);
        slot.fetch_or(0x60);
        assert_eq!(invalidated.snapshot().raw(), original.raw() | 0x60);
    }
    assert_eq!(slot.load().raw(), original.raw() | 0x60);
}

#[test]
fn a_mixed_leaf_footprint_uses_the_smallest_stride() {
    let large = PageLevel::Level1.size();
    let small = PageLevel::Level0.size();
    let mut footprint = FlushFootprint::default();
    footprint.include(VirtAddr::from(large), PageLevel::Level1);
    footprint.include(VirtAddr::from(2 * large), PageLevel::Level0);
    let token = footprint.token::<<Arch as ArchPagingMeta>::TlbFlushTok>();
    assert_eq!(
        token.scope().as_ref().unwrap().scope(),
        FlushScope::Range {
            start: VirtAddr::from(large),
            end: VirtAddr::from(2 * large + small),
            level: PageLevel::Level0,
        }
    );
    // SAFETY: this footprint describes no installed hardware mappings.
    unsafe { token.ignore() };
}

#[test]
fn unrepresentable_leaf_endpoints_require_a_global_footprint() {
    let small = PageLevel::Level0.size();
    for address in [LOW_CANONICAL_END - small, usize::MAX - (small - 1)] {
        let mut footprint = FlushFootprint::default();
        footprint.include(VirtAddr::from(address), PageLevel::Level0);
        let token = footprint.token::<<Arch as ArchPagingMeta>::TlbFlushTok>();
        assert_eq!(token.scope().as_ref().unwrap().scope(), FlushScope::All);
        // SAFETY: this footprint describes no installed hardware mappings.
        unsafe { token.ignore() };
    }
}

#[test]
fn exchanging_two_confidentiality_tags_uses_a_barrier_and_retains_history() {
    use core::sync::atomic::{AtomicUsize, Ordering};

    const PRIVATE: usize = 1 << 51;
    const SHARED: usize = 1 << 50;
    static WORD: AtomicUsize = AtomicUsize::new(0);
    static SCOPES: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct DualTag;

    impl DualTag {
        fn flush(scope: usize) {
            let word = WORD.fetch_or(0x60, Ordering::AcqRel);
            assert_eq!(word & 1, 0);
            assert!(matches!(word & (PRIVATE | SHARED), PRIVATE | SHARED));
            SCOPES.fetch_or(scope, Ordering::AcqRel);
        }
    }

    unsafe impl X86PagingParams for DualTag {
        fn private_mask() -> usize {
            PRIVATE
        }

        fn shared_mask() -> usize {
            SHARED
        }

        fn supported_flags() -> PTEntryFlags {
            PTEntryFlags::all()
        }

        fn flush_tlb_global_sync(_: FlushScope) {
            Self::flush(1);
        }

        fn flush_tlb_global_percpu(_: FlushScope) {
            Self::flush(2);
        }
    }

    type DualArch = X86Paging<DualTag>;
    WORD.store(PRIVATE | 0x2003, Ordering::Release);
    // SAFETY: static atomic storage pins the slot; this test is its only software writer.
    let slot = unsafe { PTEntryRef::<DualArch>::from_raw(WORD.as_ptr().cast()) };
    for (shared, new_tag) in [(true, SHARED), (false, PRIVATE)] {
        let flush = unsafe {
            PTPage::<DualArch, NoAllocator>::edit_leaf(
                &NoAllocator,
                slot,
                PageLevel::Level0,
                VirtAddr::from(0x2000usize),
                PageLevel::Level0,
                LeafUpdate::UpdateEncryption(shared),
                shared,
            )
        }
        .unwrap();
        flush.expect_no_flush();
        assert_eq!(slot.load().raw(), new_tag | 0x2063);
    }
    assert_eq!(SCOPES.load(Ordering::Acquire), 3);
}

#[test]
#[should_panic(expected = "index <")]
fn views_reject_indexes_outside_the_page() {
    let owner = Owner::new();
    owner.view().load(ENTRY_COUNT);
}

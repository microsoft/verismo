use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use super::{PTPage, PTPagePointer};
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy};
use crate::structs::sizes::{entry_index, PT_ENTRY_COUNT};
use crate::structs::sizes::{level_for_size, PageSize};
use crate::structs::sizes::{Size2MiB, Size4KiB};

/// Supplies either a static type-level root level or a stored runtime level.
pub(crate) trait TreeLevel {
    /// The value retained when this level is stored in a tree owner.
    type State: Copy;

    /// Inputs: stored level state.
    /// Requires: valid representation.
    /// Returns: root level.
    fn level(state: &Self::State) -> PageLevel;
}

impl<L: LevelSpec> TreeLevel for L {
    type State = ();

    /// Inputs: unit state.
    /// Requires: static level type.
    /// Returns: type-selected root level.
    fn level(_: &()) -> PageLevel {
        L::LEVEL
    }
}

impl TreeLevel for PageLevel {
    type State = PageLevel;

    /// Inputs: stored level.
    /// Requires: valid page level.
    /// Returns: stored root level.
    fn level(state: &PageLevel) -> PageLevel {
        *state
    }
}

/// A private tree that may still be changed with ordinary exclusive access.
pub(crate) struct Staged;

/// A complete tree whose entries may be observed through live atomic views.
pub(crate) struct Live;

/// Owns its root and policy-selected descendant tables, never mapped data frames.
/// Static roots store no level value; private preparations use a runtime level.
pub(crate) struct PTPageTree<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: TreeLevel = PageLevel,
    S: PagingOwnershipPolicy = KernelPolicy,
    State = Staged,
> {
    root: PhysAddr,
    level: L::State,
    policy: S,
    marker: PhantomData<(A, P, L, State)>,
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S, Staged>
{
    pub(crate) fn new_root(policy: S) -> Result<Self, PagingError> {
        let (_, root) = PTPage::<A, P>::alloc()?;
        Ok(Self { root, level: (), policy, marker: PhantomData })
    }

    /// Validates the completed staged tree and makes live access available.
    pub(crate) fn finish(self) -> Result<PTPageTree<A, P, L, S, Live>, PagingError> {
        self.validate()?;
        let (policy, root) = self.into_parts();
        Ok(PTPageTree { root, level: (), policy, marker: PhantomData })
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S, Live>
{
    /// # Safety
    /// `root` must be a currently live allocation owned by `P`, and its
    /// exclusive ownership must be transferred to the returned tree. Drop
    /// always frees the root, so the caller must neither retain ownership nor
    /// deallocate it. The root must be initialized at `L::LEVEL`, with an
    /// acyclic, correctly leveled tree whose pages stay mapped, writable and
    /// pinned for this owner.
    /// Policy-selected tables must be allocator-allocated and exclusively owned,
    /// without other parent links, when reclaimed.
    /// Suppress Drop unless those tables are owned and all their users are quiesced.
    pub(crate) unsafe fn from_root(root: PhysAddr, policy: S) -> Result<Self, PagingError> {
        let tree = ManuallyDrop::new(Self { root, level: (), policy, marker: PhantomData });
        tree.validate()?;
        Ok(ManuallyDrop::into_inner(tree))
    }
}

impl<A: ArchPagingMeta, P: DirectMappedAllocator, L: LevelSpec>
    PTPageTree<A, P, L, KernelPolicy, Live>
{
    /// Builds and validates a live tree that maps the allocator's direct map.
    pub(crate) fn new_direct_mapped(flags: A::PTFlags) -> Result<Self, PagingError> {
        let (phys, _) = P::direct_map();
        let start = P::paddr_to_vaddr(phys.start);
        let end = P::paddr_to_vaddr(phys.end);
        let small = PageLevel::Level0;
        let large = PageLevel::Level1;
        assert!(start <= end && start.is_aligned(small.size()) && end.is_aligned(small.size()));
        assert!(phys.start.is_aligned(small.size()));
        let tree = PTPageTree::<A, P, L, KernelPolicy, Staged>::new_root(KernelPolicy)?;
        {
            let mut root = tree.root();
            // SAFETY: the new tree is exclusively owned and unpublished.
            let page = unsafe { root.page_mut() };
            let parent_flags = A::PTFlags::parent_flags();
            let mut vaddr = start;
            while vaddr < end {
                let paddr = phys.start + (vaddr - start);
                let target = if L::LEVEL >= large
                    && vaddr.is_aligned(large.size())
                    && paddr.is_aligned(large.size())
                    && end - vaddr >= large.size()
                {
                    large
                } else {
                    small
                };
                // SAFETY: all pages remain exclusively owned by this tree.
                match target {
                    PageLevel::Level0 => unsafe {
                        PTPage::map_unpublished(
                            page,
                            L::LEVEL,
                            Page::<Size4KiB>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Size4KiB>::from_start_address(paddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            flags,
                            false,
                            parent_flags,
                        )
                    },
                    PageLevel::Level1 => unsafe {
                        PTPage::map_unpublished(
                            page,
                            L::LEVEL,
                            Page::<Size2MiB>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Size2MiB>::from_start_address(paddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            flags,
                            false,
                            parent_flags,
                        )
                    },
                    _ => Err(PagingError::InvalidLevel),
                }?;
                vaddr = vaddr + target.size();
            }
        }
        tree.finish()
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPageTree<A, P, PageLevel, KernelPolicy, Staged> {
    pub(crate) fn new(level: PageLevel) -> Result<Self, PagingError> {
        let (_, root) = PTPage::<A, P>::alloc()?;
        Ok(Self { root, level, policy: KernelPolicy, marker: PhantomData })
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: TreeLevel, S: PagingOwnershipPolicy, State>
    PTPageTree<A, P, L, S, State>
{
    pub(crate) fn into_parts(self) -> (S, PhysAddr) {
        let root = self.root;
        let policy = unsafe { core::ptr::read(&self.policy) };
        core::mem::forget(self);
        (policy, root)
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPageTree<A, P, PageLevel, KernelPolicy, Staged> {
    /// Transfers ownership of the whole subtree without freeing it.
    /// The recipient must retain a compatible allocator for the released pages.
    pub(crate) fn release(self) -> PhysAddr {
        let (_, root) = self.into_parts();
        root
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: TreeLevel, S: PagingOwnershipPolicy, State> Drop
    for PTPageTree<A, P, L, S, State>
{
    /// Inputs: owned tree.
    /// Requires: quiesced owned pages.
    /// Returns: nothing.
    fn drop(&mut self) {
        // SAFETY: owned tables are quiesced before Drop; shared subtrees are excluded.
        unsafe { self.root().free_children(|index| self.policy.owns_top_entry(index)) };
        // SAFETY: descendant references have ended and this root is exclusively owned.
        unsafe { P::deallocate_table_page(self.root) };
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingOwnershipPolicy, State>
    PTPageTree<A, P, L, S, State>
{
    pub(crate) fn validate(&self) -> Result<(), PagingError> {
        self.validate_page(self.root, L::LEVEL)
    }

    /// Inputs: current table and level.
    /// Requires: accessible stable tree.
    /// Returns: validation status.
    fn validate_page(&self, paddr: PhysAddr, level: PageLevel) -> Result<(), PagingError> {
        let vaddr = P::paddr_to_vaddr(paddr);
        self.validate_self_mapping(paddr, vaddr)?;
        self.validate_child_tables(level, vaddr)
    }

    /// Inputs: table addresses.
    /// Requires: stable tree.
    /// Returns: self-mapping status.
    fn validate_self_mapping(&self, paddr: PhysAddr, vaddr: VirtAddr) -> Result<(), PagingError> {
        let mut page = P::paddr_to_vaddr(self.root).as_ptr::<PTPage<A, P>>();
        let mut at = L::LEVEL;
        for _ in 0..=L::DEPTH {
            let entry = unsafe { &*page }.entry(entry_index(vaddr, at)).load();
            if entry.is_table(at) {
                page = PTPage::child_of(&entry).unwrap();
                at = at.child().unwrap();
                continue;
            }
            let translated =
                (entry.address() & !(at.size() - 1)) + (vaddr.bits() & (at.size() - 1));
            if !entry.is_leaf(at) || translated != paddr.bits() {
                return Err(PagingError::TablePageNotSelfMapped);
            }
            return Ok(());
        }
        unreachable!("self-mapping validation exceeded the tree depth")
    }

    /// Inputs: current table.
    /// Requires: stable leveled tree.
    /// Returns: child validation.
    fn validate_child_tables(&self, level: PageLevel, vaddr: VirtAddr) -> Result<(), PagingError> {
        let Some(child_level) = level.child() else {
            return Ok(());
        };
        let page = vaddr.as_ptr::<PTPage<A, P>>();
        for idx in 0..PT_ENTRY_COUNT {
            let entry = unsafe { &*page }.entry(idx).load();
            if !entry.is_table(level) {
                continue;
            }
            self.validate_page(PhysAddr::from(entry.address()), child_level)?;
        }
        Ok(())
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: TreeLevel, S: PagingOwnershipPolicy, State>
    PTPageTree<A, P, L, S, State>
{
    pub(crate) fn root_paddr(&self) -> PhysAddr {
        self.root
    }

    pub(crate) fn policy(&self) -> &S {
        &self.policy
    }

    pub(crate) fn root(&self) -> PTPagePointer<'_, A, P> {
        // SAFETY: the owner borrow pins the initialized tree and its reachable tables.
        unsafe { PTPagePointer::from_root(self.root, L::level(&self.level)) }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPageTree<A, P, PageLevel, KernelPolicy, Staged> {
    /// Adds missing tables down to `target`, without splitting existing leaves.
    pub(crate) fn grow<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        if target > self.level {
            return Err(PagingError::InvalidLevel);
        }
        self.root().grow_uninstalled(target_page, parent_flags)
    }
}

/// Inputs: entry index.
/// Requires: selected owned subtree.
/// Returns: true.
fn all_entries_owned(_: usize) -> bool {
    true
}

/// # Safety
/// The path must be exclusively owned and quiesced, without descendant
/// references surviving reclamation. `empty_entry` must reject every live mapping.
pub(crate) unsafe fn reclaim_path<A: ArchPagingMeta, P: PagingAllocator>(
    root: &PTPagePointer<'_, A, P>,
    vaddr: VirtAddr,
    empty_entry: impl Fn(PTEntry<A>) -> bool,
) -> usize {
    unsafe { reclaim_path_inner(root, vaddr, &empty_entry) }.1
}

/// Inputs: root, address, and emptiness test.
/// Requires: exclusive path.
/// Returns: emptiness and count.
unsafe fn reclaim_path_inner<A: ArchPagingMeta, P: PagingAllocator>(
    root: &PTPagePointer<'_, A, P>,
    vaddr: VirtAddr,
    empty_entry: &impl Fn(PTEntry<A>) -> bool,
) -> (bool, usize) {
    if root.level().is_leaf() {
        return (root.entries_satisfy(empty_entry), 0);
    }
    let index = entry_index(vaddr, root.level());
    let (child_pa, mut count) = match root.child(index) {
        Ok(child) => {
            // SAFETY: the child inherits the caller's ownership and exclusion.
            let (empty, count) = unsafe { reclaim_path_inner(&child, vaddr, empty_entry) };
            (empty.then(|| child.paddr()), count)
        }
        Err(_) => (None, 0),
    };
    if let Some(paddr) = child_pa {
        root.swap(index, PTEntry::empty());
        // SAFETY: the child reference has ended and the parent no longer links it.
        unsafe { P::deallocate_table_page(paddr) };
        count += 1;
    }
    (root.entries_satisfy(empty_entry), count)
}

/// # Safety
/// The nonempty range must be within this root's local offsets. Selected
/// subtrees must be exclusively owned and quiesced, without surviving child
/// references. `empty_entry` must reject every live mapping; ownership applies
/// only to root entries, with every descendant owned.
pub(crate) unsafe fn reclaim_range<A: ArchPagingMeta, P: PagingAllocator>(
    root: &PTPagePointer<'_, A, P>,
    start: usize,
    end: usize,
    owns_entry: impl Fn(usize) -> bool,
    empty_entry: impl Fn(PTEntry<A>) -> bool,
) {
    unsafe { reclaim_range_inner(root, start, end, &owns_entry, &empty_entry) };
}

/// Inputs: root, offsets, and predicates.
/// Requires: exclusive selected subtrees.
/// Returns: emptiness.
unsafe fn reclaim_range_inner<A: ArchPagingMeta, P: PagingAllocator>(
    root: &PTPagePointer<'_, A, P>,
    start: usize,
    end: usize,
    owns_entry: &impl Fn(usize) -> bool,
    empty_entry: &impl Fn(PTEntry<A>) -> bool,
) -> bool {
    if root.level().is_leaf() {
        return root.entries_satisfy(empty_entry);
    }
    let size = root.level().size();
    for index in start / size..=(end - 1) / size {
        if !owns_entry(index) {
            continue;
        }
        let base = index * size;
        let child_pa = match root.child(index) {
            Ok(child) => {
                // SAFETY: every descendant of the selected child is exclusively owned.
                let empty = unsafe {
                    reclaim_range_inner(
                        &child,
                        start.saturating_sub(base),
                        (end - base).min(size),
                        &all_entries_owned,
                        empty_entry,
                    )
                };
                empty.then(|| child.paddr())
            }
            Err(_) => None,
        };
        if let Some(paddr) = child_pa {
            root.swap(index, PTEntry::empty());
            // SAFETY: no child reference or link remains when the empty page is freed.
            unsafe { P::deallocate_table_page(paddr) };
        }
    }
    root.entries_satisfy(empty_entry)
}

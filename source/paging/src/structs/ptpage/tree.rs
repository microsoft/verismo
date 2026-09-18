use core::marker::PhantomData;

use super::{PTPage, PTPagePointer};
use crate::structs::address::{PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::level::{LevelSpec, PageLevel};
use crate::structs::os_contract::{PagingAllocator, PagingError};
#[cfg(any(feature = "concurrent", test))]
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy};
use crate::structs::sizes::{entry_index, PT_ENTRY_COUNT};
#[cfg(any(feature = "concurrent", test))]
use crate::structs::sizes::{level_for_size, PageSize};

/// Supplies either a static type-level root level or a stored runtime level.
pub(crate) trait TreeLevel {
    /// The value retained when this level is stored in a tree owner.
    type State: Copy;

    /// Inputs: stored level state; Requires: valid representation; Returns: root level.
    fn level(state: &Self::State) -> PageLevel;
}

impl<L: LevelSpec> TreeLevel for L {
    type State = ();

    /// Inputs: unit state; Requires: static level type; Returns: type-selected root level.
    fn level(_: &()) -> PageLevel {
        L::LEVEL
    }
}

impl TreeLevel for PageLevel {
    type State = PageLevel;

    /// Inputs: stored level; Requires: valid page level; Returns: stored root level.
    fn level(state: &PageLevel) -> PageLevel {
        *state
    }
}

/// Owns its root and policy-selected descendant tables, never mapped data frames.
/// Static roots store no level value; private preparations use a runtime level.
pub(crate) struct PTPageTree<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: TreeLevel = PageLevel,
    S: PagingOwnershipPolicy = KernelPolicy,
> {
    root: PhysAddr,
    level: L::State,
    policy: S,
    marker: PhantomData<(A, P, L)>,
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S>
{
    pub(crate) fn new_root(policy: S) -> Result<Self, PagingError> {
        let (_, root) = PTPage::<A, P>::alloc()?;
        Ok(Self { root, level: (), policy, marker: PhantomData })
    }

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
    pub(crate) unsafe fn from_root(root: PhysAddr, policy: S) -> Self {
        Self { root, level: (), policy, marker: PhantomData }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: TreeLevel, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S>
{
    pub(crate) fn root_paddr(&self) -> PhysAddr {
        self.root
    }

    pub(crate) fn policy(&self) -> &S {
        &self.policy
    }

    pub(crate) fn page(&self) -> *mut PTPage<A, P> {
        P::paddr_to_vaddr(self.root).as_mut_ptr()
    }

    /// # Safety
    /// The root must exclude all software and hardware access and surviving
    /// aliases for the borrow. A content lock alone does not quiesce hardware.
    pub(crate) unsafe fn page_mut(&mut self) -> &mut PTPage<A, P> {
        unsafe { &mut *self.page() }
    }

    pub(crate) fn root(&self) -> PTPagePointer<'_, A, P> {
        // SAFETY: the owner borrow pins the initialized tree and its reachable tables.
        unsafe { PTPagePointer::from_root(self.root, L::level(&self.level)) }
    }

    pub(crate) fn into_parts(self) -> (S, PhysAddr) {
        let root = self.root;
        let policy = unsafe { core::ptr::read(&self.policy) };
        core::mem::forget(self);
        (policy, root)
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPageTree<A, P> {
    pub(crate) fn new(level: PageLevel) -> Result<Self, PagingError> {
        let (_, root) = PTPage::<A, P>::alloc()?;
        Ok(Self { root, level, policy: KernelPolicy, marker: PhantomData })
    }

    /// Transfers ownership of the whole subtree without freeing it.
    /// The recipient must retain a compatible allocator for the released pages.
    pub(crate) fn release(self) -> PhysAddr {
        let (_, root) = self.into_parts();
        root
    }

    /// Adds missing tables down to `target`, without splitting existing leaves.
    #[cfg(any(feature = "concurrent", test))]
    pub(crate) fn grow<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        if target > self.level {
            return Err(PagingError::InvalidLevel);
        }
        let level = self.level;
        // SAFETY: runtime-level trees are private preparations until released.
        unsafe { Self::grow_page(self.page_mut(), level, target_page, parent_flags) }
    }

    #[cfg(any(feature = "concurrent", test))]
    /// Inputs: private page and target; Requires: exclusive unpublished tree; Returns: growth status.
    unsafe fn grow_page<PS: PageSize>(
        page: &mut PTPage<A, P>,
        level: PageLevel,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        if level <= target {
            return Ok(());
        }
        let vaddr = target_page.start_address();
        let entry = page.entry_mut(entry_index(vaddr, level));
        let child_level = level.child().unwrap();
        if entry.is_table(level) {
            // SAFETY: every reachable child belongs to this unpublished tree.
            let child = unsafe {
                &mut *P::paddr_to_vaddr(PhysAddr::from(entry.address()))
                    .as_mut_ptr::<PTPage<A, P>>()
            };
            return unsafe { Self::grow_page(child, child_level, target_page, parent_flags) };
        }
        if entry.present() {
            return Err(PagingError::NotLeafEntry);
        }
        let mut child = Self::new(child_level)?;
        child.grow(target_page, parent_flags)?;
        *entry = PTEntry::new_table(A::make_private_address(child.root_paddr()), parent_flags);
        child.release();
        Ok(())
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: TreeLevel, S: PagingOwnershipPolicy> Drop
    for PTPageTree<A, P, L, S>
{
    /// Inputs: owned tree; Requires: quiesced owned pages; Returns: nothing.
    fn drop(&mut self) {
        // SAFETY: owned tables are quiesced before Drop; shared subtrees are excluded.
        unsafe { free_children(&self.root(), |index| self.policy.owns_top_entry(index)) };
        // SAFETY: descendant references have ended and this root is exclusively owned.
        unsafe { P::deallocate_table_page(self.root) };
    }
}

/// Inputs: entry index; Requires: selected owned subtree; Returns: true.
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

/// Inputs: root, address, and emptiness test; Requires: exclusive path; Returns: emptiness and count.
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

/// Inputs: root, offsets, and predicates; Requires: exclusive selected subtrees; Returns: emptiness.
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

/// Clears owned root entries and frees their descendant tables, not data frames.
/// # Safety
/// Selected subtrees must be exclusively owned and quiesced, without
/// surviving descendant references. All their descendants must belong to the allocator.
pub(crate) unsafe fn free_children<A: ArchPagingMeta, P: PagingAllocator>(
    root: &PTPagePointer<'_, A, P>,
    owns_entry: impl Fn(usize) -> bool,
) {
    for index in 0..PT_ENTRY_COUNT {
        if !owns_entry(index) {
            continue;
        }
        if root.level().is_leaf() {
            root.store(index, PTEntry::empty());
            continue;
        }
        let entry = root.load(index);
        let child_pa = if entry.is_table(root.level()) {
            let paddr = PhysAddr::from(entry.address());
            // SAFETY: selected descendants are exclusively owned and fully quiesced.
            let child = unsafe { &mut *P::paddr_to_vaddr(paddr).as_mut_ptr::<PTPage<A, P>>() };
            unsafe { child.free_owned_children(root.level().child().unwrap(), true) };
            Some(paddr)
        } else {
            None
        };
        root.swap(index, PTEntry::empty());
        if let Some(paddr) = child_pa {
            // SAFETY: the child reference has ended and its parent link is cleared.
            unsafe { P::deallocate_table_page(paddr) };
        }
    }
}

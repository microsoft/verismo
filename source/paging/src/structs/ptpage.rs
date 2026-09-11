//! The page-table page, the frame a walk resolves to, and the edits a single
//! entry can undergo. Entries of a live table are only ever read and written
//! through raw pointers, one word at a time, because the MMU writes them too.
use core::marker::PhantomData;

use bitflags::Flags;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::sizes::ENTRY_COUNT;

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta, P: PagingHandler> {
    entries: [PTEntry<A>; ENTRY_COUNT],
    dummy: PhantomData<P>,
}

impl<A: ArchPagingMeta, P: PagingHandler> PTPage<A, P> {
    /// How many entries a table page holds: one page of the smallest size this
    /// build maps, filled with entries.
    pub const COUNT: usize = ENTRY_COUNT;

    /// A zeroed table page, and its clean physical address.
    pub fn alloc(handler: &P) -> Result<(*mut Self, PhysAddr), PagingError> {
        let paddr = handler.allocate_table_page()?;
        Ok((handler.paddr_to_vaddr(paddr).as_mut_ptr::<Self>(), paddr))
    }

    /// The table page mapped at `vaddr`.
    ///
    /// # Safety
    /// A table page must be mapped there for as long as the pointer is used.
    pub unsafe fn from_vaddr(vaddr: VirtAddr) -> *mut Self {
        vaddr.as_mut_ptr::<Self>()
    }

    /// The child table `entry` points at, or `None` if it maps a page or maps
    /// nothing. Whether an entry may be followed also depends on its level,
    /// which is the caller's business.
    pub fn child_of(handler: &P, entry: &PTEntry<A>) -> Option<*mut Self> {
        if !entry.present() || entry.huge() {
            return None;
        }
        Some(handler.paddr_to_vaddr(PhysAddr::from(entry.address())).as_mut_ptr::<Self>())
    }

    /// The entry at `index` of `page`.
    pub fn entry_ptr(page: *const Self, index: usize) -> *const PTEntry<A> {
        page.cast::<PTEntry<A>>().wrapping_add(index)
    }

    /// The entry at `index` of `page`, for writing.
    pub fn entry_ptr_mut(page: *mut Self, index: usize) -> *mut PTEntry<A> {
        page.cast::<PTEntry<A>>().wrapping_add(index)
    }

    /// Reads entry `index` of `page`.
    ///
    /// # Safety
    /// `page` must point at a mapped table page.
    pub unsafe fn read_entry(page: *const Self, index: usize) -> PTEntry<A> {
        // SAFETY: the caller vouches for `page`, and the pointer stays inside
        // it for any `index < COUNT`.
        unsafe { PTEntry::read_pte(Self::entry_ptr(page, index)) }
    }

    /// Whether no entry of `page` is present.
    ///
    /// # Safety
    /// `page` must point at a mapped table page.
    pub unsafe fn is_empty(page: *const Self) -> bool {
        // SAFETY: the caller vouches for `page`.
        (0..Self::COUNT).all(|idx| !unsafe { Self::read_entry(page, idx) }.present())
    }

    /// Frees every table page below `page`, which sits at `level`. The page
    /// itself is left to its owner.
    ///
    /// # Safety
    /// `page` must point at a mapped table page at `level` that no processor is
    /// walking and no other tree links to.
    pub unsafe fn free_lvl(handler: &P, page: *mut Self, level: PageLevel) {
        let Some(child_level) = level.child() else {
            return;
        };
        for idx in 0..Self::COUNT {
            // SAFETY: the caller vouches for `page`.
            let entry = unsafe { Self::read_entry(page, idx) };
            let Some(child) = Self::child_of(handler, &entry) else {
                continue;
            };
            // SAFETY: `child` belongs to this tree, which the caller says no
            // one is walking, so it too may be torn down.
            unsafe { Self::free_lvl(handler, child, child_level) };
            let mut cleared = entry;
            cleared.clear();
            // SAFETY: the caller vouches for `page`, and the entry is about to
            // point at a freed page, so it may not be left behind.
            unsafe { PTEntry::write_pte(Self::entry_ptr_mut(page, idx), cleared) };
            // SAFETY: nothing reaches `child` any more, and it came from
            // `allocate_table_page`.
            unsafe { handler.deallocate_table_page(PhysAddr::from(entry.address())) };
        }
    }
}

/// An entry being edited, and the level it sits at. The entry it borrows is
/// either a staged copy or a page no walker can reach yet, never a live one.
#[derive(Debug)]
pub struct Mapping<'a, A: ArchPagingMeta> {
    pub level: PageLevel,
    pub entry: &'a mut PTEntry<A>,
}

impl<'a, A: ArchPagingMeta> Mapping<'a, A> {
    pub fn new(level: PageLevel, entry: &'a mut PTEntry<A>) -> Self {
        Self { level, entry }
    }
}

/// What a walk found: a physical address, and the size of the page it sits in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Translation<A: ArchPagingMeta> {
    paddr: PhysAddr,
    level: PageLevel,
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> Translation<A> {
    pub fn new(paddr: PhysAddr, level: PageLevel) -> Self {
        Self { paddr, level, dummy: PhantomData }
    }

    /// The level the mapping was found at, which fixes the page size.
    pub fn level(&self) -> PageLevel {
        self.level
    }

    /// The address with the private tag stripped, the shared tag kept.
    pub fn page_frame(&self) -> PhysAddr {
        A::strip_confidentiality_bits(self.paddr)
    }

    /// The clean address: every architectural tag stripped.
    pub fn address(&self) -> PhysAddr {
        A::strip_shared_address_bits(self.page_frame())
    }

    pub fn size(&self) -> usize {
        self.level.size()
    }

    /// The first address of the page this frame falls in.
    pub fn start(&self) -> PhysAddr {
        PhysAddr::from(self.address().bits() & !(self.size() - 1))
    }

    pub fn end(&self) -> PhysAddr {
        self.start() + self.size()
    }
}

/// What a mapping is made of: the flags of the leaf, whether the frame is
/// shared, and the flags of any table created to reach it.
#[derive(Clone, Copy, Debug)]
pub struct MapSpec<A: ArchPagingMeta> {
    pub flags: A::PTFlags,
    pub shared: bool,
    pub parent_flags: A::PTFlags,
}

impl<A: ArchPagingMeta, P: PagingHandler> PTPage<A, P> {
    /// Builds tables from `map` down towards `target`, stopping early at a
    /// present entry or a failed allocation. Every page it creates is filled
    /// before it is linked, so no walker sees a half-built table.
    fn alloc_pte_down<'a>(
        handler: &P,
        map: Mapping<'a, A>,
        vaddr: VirtAddr,
        target: PageLevel,
        parent_flags: A::PTFlags,
    ) -> Mapping<'a, A> {
        let mut map = map;
        while map.level > target {
            if map.entry.flags().contains(A::PTFlags::PRESENT) {
                return map;
            }
            let Some(child_level) = map.level.child() else {
                return map;
            };
            let Ok((page, paddr)) = Self::alloc(handler) else {
                return map;
            };
            map.entry.set(A::make_private_address(paddr), parent_flags);
            let index = entry_index(vaddr, child_level);
            // SAFETY: `page` was just allocated and is reachable only through
            // the entry written above, which nothing else holds.
            let entry = unsafe { &mut *Self::entry_ptr_mut(page, index) };
            map = Mapping::new(child_level, entry);
        }
        map
    }

    /// Breaks the large page `entry` maps at `level` into a table one level
    /// down. The pieces inherit the flags of the entry they came from, less the
    /// size bit where the level below is the leaf.
    fn do_split(
        handler: &P,
        entry: &mut PTEntry<A>,
        level: PageLevel,
    ) -> Result<*mut Self, PagingError> {
        let Some(child_level) = level.child() else {
            return Err(PagingError::InvalidLevel);
        };
        assert!(entry.huge());
        let (page, paddr) = Self::alloc(handler)?;
        let base = entry.address() & !(level.size() - 1);
        let child_size = child_level.size();
        let child_flags = if child_level.is_leaf() {
            entry.flags().without(A::PTFlags::HUGE)
        } else {
            entry.flags()
        };
        for idx in 0..Self::COUNT {
            // SAFETY: `page` was just allocated and is linked into no tree, so
            // its entries are exclusively ours.
            let child = unsafe { &mut *Self::entry_ptr_mut(page, idx) };
            child
                .set(A::make_private_address(PhysAddr::from(base + idx * child_size)), child_flags);
        }
        entry.set(A::make_private_address(paddr), entry.flags().without(A::PTFlags::HUGE));
        Ok(page)
    }

    /// Splits `map` until `vaddr` is described by an entry at `target`.
    fn split_to<'a>(
        handler: &P,
        map: Mapping<'a, A>,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> Result<Mapping<'a, A>, PagingError> {
        let mut map = map;
        while map.level > target {
            if !map.entry.is_leaf(map.level) {
                return Err(PagingError::NotMapped);
            }
            let level = map.level;
            let page = Self::do_split(handler, map.entry, level)?;
            let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
            let index = entry_index(vaddr, child_level);
            // SAFETY: `page` is the table just split out of `map.entry`, which
            // we hold, and nothing else has reached it yet.
            let entry = unsafe { &mut *Self::entry_ptr_mut(page, index) };
            map = Mapping::new(child_level, entry);
        }
        Ok(map)
    }

    /// Maps `vaddr` to `paddr` at `target`, building the tables above it. The
    /// walk that got here reports an entry already present, so what this finds
    /// is either empty or a table it has to descend.
    pub fn do_map(
        handler: &P,
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        spec: MapSpec<A>,
    ) -> Result<(), PagingError> {
        assert!(vaddr.is_aligned(target.size()));
        assert!(paddr.is_aligned(target.size()));
        let map = Self::alloc_pte_down(handler, map, vaddr, target, spec.parent_flags);
        if map.level != target {
            return Err(PagingError::AllocFrame);
        }
        let addr = if spec.shared {
            A::make_shared_address(paddr)
        } else {
            A::make_private_address(paddr)
        };
        let flags = if target.is_leaf() { spec.flags } else { spec.flags.with(A::PTFlags::HUGE) };
        map.entry.set(addr, flags);
        Ok(())
    }

    /// Clears the entry if it maps a page of exactly `target`'s size, and
    /// returns what it held.
    pub fn do_unmap_at(map: Mapping<'_, A>, target: PageLevel) -> Option<PTEntry<A>> {
        if map.level != target || !map.entry.is_leaf(map.level) {
            return None;
        }
        let entry = *map.entry;
        map.entry.clear();
        Some(entry)
    }

    /// Clears whatever leaf the walk stopped at, and reports its level.
    pub fn do_unmap(map: Mapping<'_, A>) -> Option<PageLevel> {
        if !map.entry.is_leaf(map.level) {
            return None;
        }
        map.entry.clear();
        Some(map.level)
    }

    /// Retags the page holding `vaddr` as shared, splitting larger pages so
    /// that only a page of `target`'s size is retagged.
    pub fn do_set_shared(
        handler: &P,
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> Result<(), PagingError> {
        Self::split_to(handler, map, vaddr, target)?.entry.make_shared();
        Ok(())
    }

    /// Retags the page holding `vaddr` as private, splitting as
    /// [`Self::do_set_shared`] does.
    pub fn do_set_encrypted(
        handler: &P,
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> Result<(), PagingError> {
        Self::split_to(handler, map, vaddr, target)?.entry.make_private();
        Ok(())
    }
}

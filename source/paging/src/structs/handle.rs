//! The handle a caller holds on a page table.
//!
//! Two levels of exclusion. The operations that only walk or grow the tree take
//! `&self` and may run concurrently; reclaiming interior pages takes `&mut
//! self`, because a walker must not be standing in a page that is being freed.
//! Rust's borrow checker enforces the outer level and the OS's per-page lock
//! the inner one -- see `os_contract`.
//!
//! The tokens live in the handle rather than being threaded through every call:
//! the reader half of a table page is shareable by `&`, so `&PageTableHandle`
//! is exactly the capability a lock-free walk needs, and `&mut
//! PageTableHandle` is exactly the exclusion `free` needs.
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::map::map_at;
use crate::structs::os_contract::{PagingError, PagingHandler};
use crate::structs::range::{range_at, RangeOp};
use crate::structs::state::PTInstallState;
use crate::structs::unmap::{update_leaf_at, LeafUpdate};
use crate::structs::walk::{descend, WalkResult};

verus! {

/// A page table rooted at the architecture's top level, owned by the holder of
/// this handle.
///
/// The root page is adopted, never allocated here: whoever installs a table in
/// hardware owns its lifetime, and this handle owns only the right to read and
/// update its slots.
pub struct PageTableHandle<A: ArchPagingMeta, H: PagingHandler> {
    root: VirtAddr,
    level: PageLevel,
    page: Tracked<PTPageSharedPerm<A>>,
    install: Tracked<PTInstallState<A>>,
    dummy: PhantomData<(A, H)>,
}

impl<A: ArchPagingMeta, H: PagingHandler> PageTableHandle<A, H> {
    pub closed spec fn root_spec(&self) -> VirtAddr {
        self.root
    }

    pub closed spec fn page_spec(&self) -> PTPageSharedPerm<A> {
        self.page@
    }

    pub closed spec fn install_spec(&self) -> PTInstallState<A> {
        self.install@
    }

    /// The level of the root page, and so how deep the tree is. Nothing static
    /// fixes it: an operation that also holds the register state checks it
    /// against `PagingRegisters::level_count`.
    pub closed spec fn root_level(&self) -> PageLevel {
        self.level
    }

    /// Whether the hardware may be walking this tree.
    pub open spec fn installed(&self) -> bool {
        self.install_spec().installed()
    }

    /// The tokens describe the root page, and the OS's lock for that address
    /// guards its writers.
    pub open spec fn inv(&self) -> bool {
        &&& level_geometry_wf::<A>()
        &&& self.page_spec().wf()
        &&& self.page_spec().level == self.root_level()
        &&& self.page_spec().base == self.root_spec()@
        &&& self.install_spec().root_frame() == H::spec_vaddr_to_paddr(self.root_spec()@)
    }

    #[verifier::when_used_as_spec(root_spec)]
    pub fn root(&self) -> (ret: VirtAddr)
        returns
            self.root_spec(),
    {
        self.root
    }

    /// Adopts a root page whose slots the caller already owns.
    pub fn new(
        root: VirtAddr,
        level: PageLevel,
        Tracked(page): Tracked<PTPageSharedPerm<A>>,
        Tracked(install): Tracked<PTInstallState<A>>,
    ) -> (ret: Self)
        requires
            level_geometry_wf::<A>(),
            page.wf(),
            page.base == root@,
            page.level == level,
            install.root_frame() == H::spec_vaddr_to_paddr(root@),
        ensures
            ret.inv(),
            ret.root_spec() == root,
            ret.root_level() == level,
            ret.page_spec() == page,
            ret.install_spec() == install,
    {
        PageTableHandle {
            root,
            level,
            page: Tracked(page),
            install: Tracked(install),
            dummy: PhantomData,
        }
    }

    /// Where `vaddr` currently leads: the entry the hardware walker would stop
    /// at, and the page holding it.
    ///
    /// Takes `&self`, so any number of threads may query at once, and takes no
    /// lock: what comes back is an observation of the tree, and only what
    /// `entry_step` preserves stays true of it afterwards.
    pub fn query(&self, vaddr: VirtAddr) -> (ret: WalkResult<A>)
        requires
            self.inv(),
        ensures
            ret.level.spec_depth() <= self.root_level().spec_depth(),
            ret.entry.is_table_spec() ==> ret.level.spec_is_leaf(),
    {
        descend::<A, H>(self.root, self.level, self.borrow_page(), vaddr)
    }

    /// The frame `vaddr` maps to, or why it does not map.
    ///
    /// A present entry above the leaf level maps a large page; at the leaf
    /// every present entry maps one. An entry that still points at a table at
    /// the leaf level is not a mapping the walk may follow -- there the bit
    /// that would say "table" is PAT.
    pub fn translate(&self, vaddr: VirtAddr) -> (ret: Result<PhysAddr, PagingError>)
        requires
            self.inv(),
    {
        let stop = self.query(vaddr);
        if stop.entry.present() && !stop.entry.is_table() {
            Ok(PhysAddr::from(stop.entry.address()))
        } else {
            Err(PagingError::NotMapped)
        }
    }

    /// Maps `vaddr` to `paddr` at `target`, building the tables in between.
    ///
    /// Takes `&self`: mapping only grows the tree, and a walker standing in a
    /// page is unaffected by a page being linked below it. Fails if the address
    /// already maps -- see [`map_at`].
    ///
    /// `paddr` carries whatever tag the caller wants the mapping to have; only
    /// the bits outside the address field are dropped. Above the leaf level the
    /// huge bit is set here, because at those levels it is what distinguishes a
    /// mapping from a table pointer.
    pub fn map(
        &self,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        flags: A::PTFlags,
    ) -> (ret: Result<(), PagingError>)
        requires
            self.inv(),
            paddr@ & !A::spec_address_mask() == 0,
    {
        let leaf_flags = if target.is_leaf() {
            flags
        } else {
            flags.with(A::PTFlags::HUGE)
        };
        let entry = PTEntry::<A>::new_leaf(paddr, leaf_flags);
        map_at::<A, H>(self.root, self.level, self.borrow_page(), vaddr, target, entry)
    }

    /// Removes the mapping `vaddr` leads to, returning the entry that was
    /// there so the caller can reclaim the frame it named.
    ///
    /// The TLB still holds the old translation afterwards: nothing here
    /// invalidates it, because which processors need telling is the OS's to
    /// know.
    pub fn unmap(&self, vaddr: VirtAddr) -> (ret: Result<PTEntry<A>, PagingError>)
        requires
            self.inv(),
        ensures
            ret matches Ok(old) ==> !old.is_table_spec(),
    {
        update_leaf_at::<A, H>(self.root, self.level, self.borrow_page(), vaddr, LeafUpdate::Clear)
    }

    /// Replaces the permissions of the mapping `vaddr` leads to, keeping the
    /// frame, and returns the entry that was there.
    pub fn protect(&self, vaddr: VirtAddr, flags: A::PTFlags) -> (ret: Result<
        PTEntry<A>,
        PagingError,
    >)
        requires
            self.inv(),
        ensures
            ret matches Ok(old) ==> !old.is_table_spec(),
    {
        update_leaf_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vaddr,
            LeafUpdate::SetFlags(flags),
        )
    }

    /// Maps `[vstart, vend)` to the physical range starting at `paddr`.
    ///
    /// One pass over the tree rather than one walk per page, and one
    /// acquisition of each leaf page's lock rather than one per entry -- see
    /// [`range_at`]. Fails, leaving what it has already written in place, on
    /// the first address that already maps.
    pub fn map_range(
        &self,
        vstart: usize,
        vend: usize,
        paddr: usize,
        target: PageLevel,
        flags: A::PTFlags,
    ) -> (ret: Result<(), PagingError>)
        requires
            self.inv(),
            vstart <= vend,
            paddr + (vend - vstart) <= usize::MAX,
    {
        let leaf_flags = if target.is_leaf() {
            flags
        } else {
            flags.with(A::PTFlags::HUGE)
        };
        range_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            target,
            RangeOp::Map { paddr, flags: leaf_flags },
        )
    }

    /// Clears every mapping in `[vstart, vend)` that was installed at `target`.
    ///
    /// Addresses in the range that do not map are left alone, so a caller need
    /// not know which parts of a region were mapped. As with [`Self::unmap`],
    /// the TLB is not invalidated here.
    pub fn unmap_range(&self, vstart: usize, vend: usize, target: PageLevel) -> (ret: Result<
        (),
        PagingError,
    >)
        requires
            self.inv(),
            vstart <= vend,
    {
        range_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            target,
            RangeOp::Unmap,
        )
    }

    /// Replaces the permissions of every mapping in `[vstart, vend)` that was
    /// installed at `target`, keeping the frames.
    pub fn protect_range(
        &self,
        vstart: usize,
        vend: usize,
        target: PageLevel,
        flags: A::PTFlags,
    ) -> (ret: Result<(), PagingError>)
        requires
            self.inv(),
            vstart <= vend,
    {
        let leaf_flags = if target.is_leaf() {
            flags
        } else {
            flags.with(A::PTFlags::HUGE)
        };
        range_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            target,
            RangeOp::Protect { flags: leaf_flags },
        )
    }

    /// The root tokens, as a walk needs them: shared, so several walks may hold
    /// them at once.
    pub fn borrow_page(&self) -> (ret: Tracked<&PTPageSharedPerm<A>>)
        ensures
            *ret@ == self.page_spec(),
    {
        Tracked(self.page.borrow())
    }

    /// Gives the root tokens back, dissolving the handle.
    pub fn into_parts(self) -> (ret: (
        VirtAddr,
        PageLevel,
        Tracked<PTPageSharedPerm<A>>,
        Tracked<PTInstallState<A>>,
    ))
        ensures
            ret.0 == self.root_spec(),
            ret.1 == self.root_level(),
            ret.2@ == self.page_spec(),
            ret.3@ == self.install_spec(),
    {
        (self.root, self.level, self.page, self.install)
    }
}

} // verus!

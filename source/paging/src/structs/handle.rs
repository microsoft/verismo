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
use machine_model::arch::x86_64::Cr3;
use machine_model::register::RustRegisterPointsTo;

use crate::arch::x86_64::reg_contract::cr3_root_frame;
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::free::free_page_tree;
use crate::structs::level::PageLevel;
use crate::structs::map::map_at;
use crate::structs::os_contract::{PTPageInit, PageLock, PagingError, PagingHandler};
use crate::structs::range::{leaf_entry, range_at, RangeOp};
use crate::structs::region::map_region;
use crate::structs::state::PTInstallState;
use crate::structs::tlb::MayNeedFlush;
use crate::structs::unmap::{update_leaf_at, LeafUpdate};
use crate::structs::update::set_leaf_slot;
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
        (PTEntry<A>, MayNeedFlush),
        PagingError,
    >)
        requires
            self.inv(),
            vaddr@ < usize::MAX,
        ensures
            ret matches Ok((old, _)) ==> !old.is_table_spec(),
    {
        match update_leaf_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vaddr,
            LeafUpdate::SetFlags(flags),
        ) {
            Err(e) => Err(e),
            Ok(old) => Ok((old, MayNeedFlush::range(vaddr.bits(), vaddr.bits() + 1))),
        }
    }

    /// Moves the page `vaddr` leads to between private and shared memory,
    /// keeping its frame and its permissions, and returns the entry that was
    /// there.
    ///
    /// Nothing about the frame changes except the tag the hardware reads to
    /// decide whether to decrypt it -- which is precisely why the old
    /// translation must not survive anywhere: a frame reachable under two tags
    /// at once is the same memory seen two ways, and only one of them is the
    /// one the caller asked for.
    pub fn set_sharing(&self, vaddr: VirtAddr, shared: bool) -> (ret: Result<
        (PTEntry<A>, MayNeedFlush),
        PagingError,
    >)
        requires
            self.inv(),
            vaddr@ < usize::MAX,
        ensures
            ret matches Ok((old, _)) ==> !old.is_table_spec(),
    {
        match update_leaf_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vaddr,
            LeafUpdate::SetSharing { shared },
        ) {
            Err(e) => Err(e),
            Ok(old) => Ok((old, MayNeedFlush::range(vaddr.bits(), vaddr.bits() + 1))),
        }
    }

    /// The frame the hardware is told to start walking from: what goes in
    /// `CR3`.
    pub fn root_frame(&self) -> (ret: PhysAddr)
        requires
            self.inv(),
        ensures
            ret@ == self.install_spec().root_frame(),
    {
        H::vaddr_to_paddr(self.root)
    }

    /// Records that the paging-root register now names this tree, so that the
    /// operations which may not run under a walking processor start refusing.
    ///
    /// Loading the register is the caller's; this is the bookkeeping that goes
    /// with it, and it is checked rather than believed -- the register token
    /// has to say that the register really holds this tree's root.
    pub fn install(&mut self, Tracked(cr3): Tracked<&RustRegisterPointsTo<Cr3>>)
        requires
            old(self).inv(),
            cr3_root_frame::<A>(cr3.value()) == old(self).install_spec().root_frame(),
        ensures
            final(self).inv(),
            final(self).installed(),
            final(self).root_spec() == old(self).root_spec(),
            final(self).root_level() == old(self).root_level(),
            final(self).page_spec() == old(self).page_spec(),
    {
        let root = H::vaddr_to_paddr(self.root);
        PTInstallState::<A>::mark_installed(Tracked(self.install.borrow_mut()), root, Tracked(cr3));
    }

    /// Records that no processor's paging-root register names this tree any
    /// more, which is what lets it be taken apart.
    ///
    /// TRUSTED in the same way [`PTInstallState::mark_uninstalled`] is: one
    /// register state cannot witness the absence of this root from every
    /// processor, so the caller carries that argument.
    pub proof fn uninstall(tracked &mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            !final(self).installed(),
            final(self).root_spec() == old(self).root_spec(),
            final(self).root_level() == old(self).root_level(),
            final(self).page_spec() == old(self).page_spec(),
    {
        PTInstallState::mark_uninstalled(self.install.borrow_mut());
    }

    /// Maps `[vstart, vend)` to the physical range starting at `paddr`.    ///
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

    /// Maps `[vstart, vend)` to the physical range at `paddr`, choosing the
    /// page size rather than being told it.
    ///
    /// `big` is the size to prefer and `small` the size to fall back to: the
    /// middle of the region is mapped with the first wherever it can be, the
    /// ends with the second. "Wherever it can be" is the condition
    /// [`map_region`] states -- the virtual and physical addresses have to
    /// agree on where a big block begins.
    pub fn map_region(
        &self,
        vstart: usize,
        vend: usize,
        paddr: usize,
        flags: A::PTFlags,
        big: PageLevel,
        small: PageLevel,
    ) -> (ret: Result<(), PagingError>)
        requires
            self.inv(),
            vstart <= vend,
            paddr + (vend - vstart) <= usize::MAX,
    {
        map_region::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            paddr,
            flags,
            big,
            small,
        )
    }

    /// Clears every mapping in `[vstart, vend)` that was installed at `target`.
    ///
    /// Addresses in the range that do not map are left alone, so a caller need
    /// not know which parts of a region were mapped. As with [`Self::unmap`],
    /// the TLB is not invalidated here.
    pub fn unmap_range(&self, vstart: usize, vend: usize, target: PageLevel) -> (ret: Result<
        MayNeedFlush,
        PagingError,
    >)
        requires
            self.inv(),
            vstart <= vend,
    {
        match range_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            target,
            RangeOp::Unmap,
        ) {
            Err(e) => Err(e),
            Ok(()) => Ok(MayNeedFlush::range(vstart, vend)),
        }
    }

    /// Replaces the permissions of every mapping in `[vstart, vend)` that was
    /// installed at `target`, keeping the frames.
    pub fn protect_range(
        &self,
        vstart: usize,
        vend: usize,
        target: PageLevel,
        flags: A::PTFlags,
    ) -> (ret: Result<MayNeedFlush, PagingError>)
        requires
            self.inv(),
            vstart <= vend,
    {
        let leaf_flags = if target.is_leaf() {
            flags
        } else {
            flags.with(A::PTFlags::HUGE)
        };
        match range_at::<A, H>(
            self.root,
            self.level,
            self.borrow_page(),
            vstart,
            vend,
            target,
            RangeOp::Protect { flags: leaf_flags },
        ) {
            Err(e) => Err(e),
            Ok(()) => Ok(MayNeedFlush::range(vstart, vend)),
        }
    }

    /// Clears every mapping in `[vstart, vend)`, whatever page sizes it was
    /// built out of.
    ///
    /// Written at the smallest page size, which is not the same as assuming
    /// the region is mapped that way: a larger mapping the range covers whole
    /// is cleared where it stands, and one the range ends inside is split
    /// first, so only the addresses the caller named stop mapping.
    pub fn unmap_region(&self, vstart: usize, vend: usize) -> (ret: Result<
        MayNeedFlush,
        PagingError,
    >)
        requires
            self.inv(),
            vstart <= vend,
    {
        self.unmap_range(vstart, vend, PageLevel::Level0)
    }

    /// Replaces the permissions of every mapping in `[vstart, vend)`, whatever
    /// page sizes it was built out of.
    ///
    /// Splits where the range ends inside a larger mapping, for the reason
    /// [`Self::unmap_region`] gives: the addresses outside the range must keep
    /// the permissions they had.
    pub fn protect_region(&self, vstart: usize, vend: usize, flags: A::PTFlags) -> (ret: Result<
        MayNeedFlush,
        PagingError,
    >)
        requires
            self.inv(),
            vstart <= vend,
    {
        self.protect_range(vstart, vend, PageLevel::Level0, flags)
    }

    /// Frees every table page of the tree and gives the root's frame back as
    /// plain ownership.
    ///
    /// Consumes the handle, which is the outer level of exclusion at its
    /// strongest: no walk, map or unmap can be in progress, because every one
    /// of them borrows the handle. It also requires that the tree is not
    /// installed -- Rust cannot see the hardware walker, so that has to be
    /// said.
    ///
    /// The root frame comes back rather than being deallocated: the root was
    /// adopted, not allocated here, so returning it is the caller's to decide.
    pub fn free(self) -> (ret: (Tracked<PTPageInit<A>>, Tracked<PTInstallState<A>>))
        requires
            self.inv(),
            !self.installed(),
        ensures
            ret.0@.wf_owned(),
            ret.0@.base == self.root_spec()@,
    {
        let (root, level, page, install) = self.into_parts();
        let lock = H::page_lock(root);
        let writers = lock.lock::<A>(Tracked(page.borrow()));
        let init = free_page_tree::<A, H>(root, level, page, writers);
        (init, install)
    }

    /// Installs the self-map: a root entry pointing at the root page itself,
    /// so the tree's own pages are readable at a fixed virtual address.
    ///
    /// The entry is deliberately *not* a table pointer as this crate defines
    /// one. A table entry escrows the tokens of the page it points at, and the
    /// root's tokens are held by this handle -- an entry escrowing them would
    /// have to contain itself. What the self-map gives is access to the tables
    /// as data, which is exactly a leaf mapping of the root frame, and a walk
    /// stops at it rather than descending.
    pub fn install_self_map(&self, index: usize, flags: A::PTFlags) -> (ret: Result<
        (),
        PagingError,
    >)
        requires
            self.inv(),
            index < PTEntry::<A>::count_per_page(),
    {
        let frame = H::vaddr_to_paddr(self.root);
        let entry = leaf_entry::<A>(frame.bits() | A::private_pte_mask(), flags);
        let lock = H::page_lock(self.root);
        let Tracked(mut writers) = lock.lock::<A>(self.borrow_page());
        let ret = set_leaf_slot::<A>(
            self.root,
            index,
            self.borrow_page(),
            Tracked(&mut writers),
            entry,
        );
        lock.unlock::<A>(self.borrow_page(), Tracked(writers));
        ret
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

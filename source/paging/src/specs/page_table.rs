//! What a page table lets you do, stated as a protocol over permissions.
//!
//! A [`GeneralPointsTo`] is a set of aliasing pointers to one piece of memory.
//! Editing a page table is what changes that set, and this trait is the only
//! way it may change: [`PageTableHandle::map`] adds a pointer,
//! [`PageTableHandle::unmap`] removes one.
//!
//! # Why mapping consumes a token
//!
//! An alias is a claim about the page tables, and a permission holds nothing
//! that stops them changing underneath it. So the right to a virtual address
//! has to be a resource, not a side condition: `map` takes a [`VirtAddrTok`]
//! for the range and keeps it, and `unmap` is the only way to get it back.
//! Whoever wants to tear a mapping down must therefore obtain the token from
//! the alias holder, who gives up the alias in the same step.
//!
//! # Where the physical identity lives
//!
//! Both operations need to know which physical memory is involved, and a
//! [`PhysAddrTok`] is what says who owns it. It sits in one of two places, and
//! that is the whole difference between the two variants of
//! [`MapVirtPhysToks`]:
//!
//! - **Inside the permission.** [`GeneralPointsTo::has_pinned_phys_addr`] holds,
//!   the frame backing the memory cannot change, and the permission is a
//!   [`PhysPointsTo`]. This covers the direct map, `vmalloc`, fixed mappings and
//!   the recursive map -- everything whose backing frame is decided once.
//! - **Outside it.** The permission is unpinned and owns no physical identity,
//!   so the caller lends one for the duration of the call. This is demand
//!   paging: the token lives in the kernel's page metadata precisely because the
//!   frame may be replaced later, which is exactly what a pinned permission
//!   forbids.
#[cfg(verus_only)]
use crate::specs::points_to::page_offset_of;
#[cfg(verus_only)]
use crate::specs::points_to::page_start_of;
use crate::specs::points_to::{GeneralPointsTo, PhysAddrTok, PhysPointsTo, VirtAddrTok};
use crate::structs::frame::PhysFrame;
use crate::structs::page::Page;
use crate::structs::sizes::{MinPageSize, PAGE_SIZE};
use crate::ArchPagingMeta;
use vstd::prelude::*;
use vstd::raw_ptr::MemContents;

verus! {

/// The claims a caller must present to install a mapping: the right to the
/// virtual range, and the right to the physical range.
///
/// The two variants are two different operations, which is why they carry
/// different things:
///
/// - `MapPinnedPfn` *adds a name*. The frame is settled, so the caller supplies
///   a fresh [`VirtAddrTok`] for the new virtual range and the permission's own
///   pinned identity fixes the frame.
/// - `MapUnpinnedPfn` *repoints an existing name*. The virtual range is already
///   claimed inside the permission, so no new token is needed; what changes is
///   the frame, and its claim is lent mutably by the party that owns it -- the
///   kernel's page metadata.
pub tracked enum MapVirtPhysToks<'a, T> {
    /// The permission is pinned, so it carries the physical claim itself. The
    /// direct map, `vmalloc`, fixed mappings and the recursive map -- types 1-4.
    MapPinnedPfn(VirtAddrTok, PhysPointsTo<T>),
    /// The permission is unpinned and owns no physical identity, so the frame
    /// claim is lent mutably by whoever does own it. Demand paging -- type 5.
    MapUnpinnedPfn(GeneralPointsTo<T>, &'a mut PhysAddrTok),
}

impl<'a, T> MapVirtPhysToks<'a, T> {
    /// Whether the variant matches the permission it carries. `MapPinnedPfn`
    /// needs no clause: being pinned is [`PhysPointsTo`]'s type invariant.
    pub open spec fn wf(&self) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, _) => true,
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => !target.has_pinned_phys_addr(),
        }
    }

    /// Whether these are the claims for pointing `vpage` at `frame`.
    ///
    /// Page granularity, not `size_of::<T>()`: the MMU maps pages, so a caller
    /// that held only part of a page could still change what the rest of it
    /// reaches.
    pub open spec fn for_page_and_frame(
        &self,
        vpage: Page<MinPageSize>,
        frame: PhysFrame<MinPageSize>,
    ) -> bool {
        &&& self.owns_virt_page(vpage)
        &&& self.owns_phys_frame(frame)
    }

    /// Whether the caller may name `vpage`.
    ///
    /// Adding a name demands the whole page: a fresh [`VirtAddrTok`] spanning
    /// it. Repointing one demands only that the permission is already reached
    /// through that page, since the name is not what is changing.
    pub open spec fn owns_virt_page(&self, vpage: Page<MinPageSize>) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(virt, _) => virt.is_range(
                vpage@ as int,
                PAGE_SIZE as int,
            ),
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => exists|p: *mut T| #[trigger]
                target.covers(p) && page_start_of(p@.addr as int) == vpage@ as int,
        }
    }

    /// Whether the caller owns every physical address in `frame`, wherever the
    /// claim is kept.
    pub open spec fn owns_phys_frame(&self, frame: PhysFrame<MinPageSize>) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target.pinned_to_frame(frame@),
            MapVirtPhysToks::MapUnpinnedPfn(_, phys) => phys.is_range(
                frame@ as int,
                PAGE_SIZE as int,
            ),
        }
    }

    /// Whether the caller may name `ptr`: a fresh claim when adding a name,
    /// the permission's existing claim when repointing one.
    pub open spec fn owns_virt_range(&self, ptr: *mut T) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(virt, _) => virt.is_range(
                ptr@.addr as int,
                size_of::<T>() as int,
            ),
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => target.covers(ptr),
        }
    }

    /// Whether the caller owns the physical addresses at `pa`.
    pub open spec fn owns_phys_range(&self, pa: usize) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target.is_at_phys_addr(pa as int),
            MapVirtPhysToks::MapUnpinnedPfn(_, phys) => phys.is_range(
                pa as int,
                size_of::<T>() as int,
            ),
        }
    }

    /// Whether the target's physical identity travels with the permission.
    pub open spec fn is_pinned(&self) -> bool {
        self is MapPinnedPfn
    }

    /// The names the target already has.
    pub open spec fn target_ptrs(&self) -> Set<*mut T> {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target.ptrs(),
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => target.ptrs(),
        }
    }

    pub open spec fn opt_value(&self) -> MemContents<T> {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target.opt_value(),
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => target.opt_value(),
        }
    }

    /// The frames backing the target. Empty for an unpinned target, which is
    /// what owning no physical identity means.
    pub open spec fn frames(&self) -> Seq<PhysFrame<MinPageSize>> {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target.frames(),
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => target.frames(),
        }
    }

    /// Whether the MMU reads the target as part of a page table.
    pub open spec fn is_pt(&self) -> bool {
        match self {
            MapVirtPhysToks::MapPinnedPfn(_, target) => target@.is_pt,
            MapVirtPhysToks::MapUnpinnedPfn(target, _) => target@.is_pt,
        }
    }
}

/// The page-table operations of one address space.
///
/// An implementation owns whatever it takes to edit the tables; this trait says
/// only what editing them does to the permissions that describe the memory
/// mapped.
pub trait PageTableHandle<A: ArchPagingMeta>: Sized {
    /// Whether the handle describes a well-formed address space.
    spec fn wf(&self) -> bool;

    /// Whether this address space translates `vaddr` to `pa` right now.
    spec fn translates(&self, vaddr: usize, pa: usize) -> bool;

    /// Install a translation from `ptr` to `pa`: a new name for pinned memory,
    /// a new frame for unpinned memory.
    ///
    /// The virtual claim in `toks` is kept, not returned: an alias is a claim
    /// about the page tables, and nothing in a permission stops them changing
    /// underneath it. Holding the right to the address is what makes the new
    /// alias durable, and [`Self::unmap`] is the only way to get it back.
    proof fn map<'a, T>(
        tracked &mut self,
        ptr: *mut T,
        pa: usize,
        tracked toks: MapVirtPhysToks<'a, T>,
    ) -> (tracked ret: GeneralPointsTo<T>)
        requires
            old(self).wf(),
            toks.wf(),
            toks.owns_virt_range(ptr),
            toks.owns_phys_range(pa),
            toks.is_pinned() ==> !toks.target_ptrs().contains(ptr),
            page_offset_of(ptr@.addr as int) == page_offset_of(pa as int),
        ensures
            final(self).wf(),
            final(self).translates(ptr@.addr, pa),
            ret.ptrs() == toks.target_ptrs().insert(ptr),
            ret.has_pinned_phys_addr() == toks.is_pinned(),
            ret.frames() == toks.frames(),
            ret.opt_value() == toks.opt_value(),
            ret@.is_pt == toks.is_pt(),
    ;

    /// Take away one of the names this memory has, and hand back the right to
    /// the address.
    ///
    /// Not the last name: unmapping the only pointer to unpinned memory would
    /// leave a permission that names nothing at all, neither a way in nor a
    /// place. Pinned memory may drop to no pointers, because its physical
    /// address still names it -- that is what an owned but unmapped frame is.
    proof fn unmap<T>(
        tracked &mut self,
        ptr: *mut T,
        tracked target: GeneralPointsTo<T>,
    ) -> (tracked ret: (GeneralPointsTo<T>, VirtAddrTok))
        requires
            old(self).wf(),
            target.covers(ptr),
            target.has_pinned_phys_addr() || exists|p: *mut T| target.covers(p) && p != ptr,
        ensures
            final(self).wf(),
            forall|pa: usize| !final(self).translates(ptr@.addr, pa),
            ret.0.ptrs() == target.ptrs().remove(ptr),
            ret.0.frames() == target.frames(),
            ret.0.opt_value() == target.opt_value(),
            ret.0@.is_pt == target@.is_pt,
            ret.1.is_range(ptr@.addr as int, size_of::<T>() as int),
    ;
}

} // verus!

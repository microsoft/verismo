//! What a handover leaves the OS.
//!
//! Two kinds of memory, and they are opposites. A page table is *reachable and
//! pinned*: the firmware left it at some virtual address, and being a table it
//! can never move. A free frame is *owned and unreachable*: the OS has it, but
//! no virtual address translates to it yet, so nothing can read or write it
//! until a mapping is installed.
//!
//! Firmware leaves the tables reachable one of two ways, and this module
//! describes both. A [`SelfMap`] points one root slot back at the root, which
//! exposes the root table and nothing else. A [`DirectMap`] maps a region of
//! physical memory straight through at addresses its own `pa_to_va` computes,
//! which exposes every table in that region at once. A handover has at least one
//! of them -- with neither, no walk could read its own root.
//!
//! A free frame is a [`PhysPointsTo`]: pinned, so its physical address names
//! it, which is the only name it has. The difference from a mapped page is
//! entirely in `ptrs` -- that is the point of a permission carrying a *set* of
//! pointers, since the empty set is a perfectly good element of it and is
//! exactly what "not mapped" means.
use crate::entry::PTEntry;
use crate::level::PageLevel;
use crate::specs::points_to::{page_start_of, Mapping, PhysPointsTo, VirtAddrTok};
use crate::structs::arch_contract::*;
use crate::structs::frame::PhysFrame;
use crate::structs::ptpage::PTPage;
use crate::ArchPagingMeta;
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

/// Everything the firmware handed over for one region: the right to its virtual
/// addresses, and both halves of the record for every page in it.
///
/// This crate has no way to build one, and deliberately does not assume one
/// either. [`VirtAddrTok`] and the mapping records are each
/// pinned to an identity fixed by their type, so no allocation could ever be
/// shown to produce *the* token; the first ones have to come from outside.
/// [`Self::init_wf`] is this crate's side of that handshake -- it says what a
/// handover has to look like to be usable, without claiming that one exists.
///
/// The trusted startup shim supplies the value and is responsible for supplying
/// it *once*: two handovers covering one address would give two permissions
/// over the same pointer, and [`crate::specs::points_to::GeneralPointsTo::is_disjoint`] would then prove those
/// pointers disjoint, which is to say prove `false`.
#[verifier::reject_recursive_types(A)]
pub tracked struct InitialVirtMappings<A: ArchPagingMeta> {
    /// The pages handed over. Not a range: what the firmware leaves usable need
    /// not be contiguous, so the set is the only honest description.
    pub ghost vpages: Set<int>,
    /// The virtual addresses, as one token.
    pub tracked virt: VirtAddrTok,
    /// The half of each page's record that the permissions share out, per page.
    /// A permission carved from this takes the part of it that matches the bytes
    /// it owns; see [`Mapping::share_of`].
    pub tracked records: Map<int, Mapping<A>>,
    /// The half of each page's record the page table keeps.
    pub tracked auths: Map<int, Mapping<A>>,
}

impl<A: ArchPagingMeta> InitialVirtMappings<A> {
    /// The pages this covers.
    pub open spec fn dom(&self) -> Set<int> {
        self.vpages
    }

    /// What the entry point must hand this crate: the virtual addresses, and a
    /// matched pair of record halves for every page in [`Self::dom`].
    ///
    /// No physical range: the physical side of the handover arrives as the
    /// [`PhysPointsTo`]s in [`InitialPermissions::free_frames`], each already
    /// carrying its own claim on a frame.
    ///
    /// Nothing here says which variable a share belongs to: [`Mapping`] pins
    /// that in its type invariant, so a share for the right page is a share of
    /// the right variable by construction. What is left to say is that the two
    /// halves account for the whole of it, or the page could never be repointed.
    pub open spec fn init_wf(&self) -> bool {
        &&& self.records.dom() =~= self.dom()
        &&& self.auths.dom() =~= self.dom()
        &&& forall|vpage: int| #[trigger]
            self.dom().contains(vpage) ==> self.records[vpage].vpage_addr() == vpage
        &&& forall|vpage: int| #[trigger]
            self.dom().contains(vpage) ==> self.auths[vpage].vpage_addr() == vpage
        &&& forall|vpage: int| #[trigger]
            self.dom().contains(vpage) ==> self.records[vpage].share() == Mapping::<A>::share_of(
                page_size::<A>() as int,
            )
        &&& forall|vpage: int| #[trigger]
            self.dom().contains(vpage) ==> self.auths[vpage].share() == Mapping::<A>::share_of(
                page_size::<A>() as int,
            )
    }
}

/// Virtual address at which a self map installed at slot `k` exposes the root
/// table, for the levels from `level` down to the leaf.
///
/// Every index of the address is `k`, because each step of the walk re-reads
/// the self entry and lands back on the root. It is the one address a walk can
/// reach the root at when the root maps nothing else.
pub open spec fn self_map_base<A: ArchPagingMeta>(k: usize, level: PageLevel) -> nat
    decreases level.depth(),
{
    let here = k * pow2(level_shift::<A>(level.depth() as nat));
    match level.spec_child() {
        Some(child) => (here + self_map_base::<A>(k, child)) as nat,
        None => here as nat,
    }
}

/// Virtual address of entry `slot` of a table page exposed at `base`.
pub open spec fn entry_vaddr_at<A: ArchPagingMeta>(base: usize, slot: nat) -> int {
    slot_addr::<A>(base, slot as int)
}

/// What every table entry the firmware hands over looks like: a page-table
/// entry, pinned to its own frame at its own slot, and reachable at exactly the
/// one virtual address the handover exposes it at.
///
/// Shared by both ways in, because the two differ only in what that address is.
/// The `forall`/`exists` pair is the whole of "exactly one alias": no alias the
/// handover does not account for, and at least one, or the entry could not be
/// read at all.
pub open spec fn table_entry_wf<A: ArchPagingMeta>(
    entry: PhysPointsTo<PTEntry<A>, A>,
    frame: usize,
    slot: nat,
    vaddr: int,
) -> bool {
    &&& entry.is_pt()
    &&& entry.is_init()
    &&& entry.pinned_to_frame(frame)
    &&& entry.is_at_phys_addr(slot_addr::<A>(frame, slot as int))
    &&& forall|p: *mut PTEntry<A>| #[trigger] entry.covers(p) ==> p@.addr == vaddr
    &&& exists|p: *mut PTEntry<A>| #[trigger] entry.covers(p)
}

/// One root slot pointing back at the root frame: the root table, and only the
/// root table, is readable.
///
/// A walk that re-reads the self entry at every level lands back on the root, so
/// [`self_map_base`] is the single address the root appears at.
#[verifier::reject_recursive_types(A)]
pub tracked struct SelfMap<A: ArchPagingMeta> {
    /// Slot of the root table that points back at the root.
    pub ghost slot: nat,
    /// One permission per entry of the root table, keyed by slot. Pinned: the
    /// MMU walks the table by physical address, so a table page whose frame
    /// could move is not a table page.
    pub tracked entries: Map<nat, PhysPointsTo<PTEntry<A>, A>>,
}

impl<A: ArchPagingMeta> SelfMap<A> {
    /// Where the self map exposes the root table.
    pub open spec fn base(&self, max_level: PageLevel) -> usize {
        self_map_base::<A>(self.slot as usize, max_level) as usize
    }

    /// Virtual address of the root table's entry `slot`, as the self map
    /// exposes it.
    pub open spec fn entry_vaddr(&self, max_level: PageLevel, slot: nat) -> int {
        entry_vaddr_at::<A>(self.base(max_level), slot)
    }

    /// The one virtual page the root table occupies.
    ///
    /// Every entry of the table shares it: the self map exposes the whole table
    /// at [`Self::base`], and a table is exactly one page, so the slot only
    /// picks an offset within this page.
    pub open spec fn vpage(&self, max_level: PageLevel) -> int {
        page_start_of::<A>(self.base(max_level) as int)
    }

    /// Every entry of the root table is well formed at the address the self map
    /// exposes it at, and the root maps itself and nothing else: the self slot
    /// holds a table entry pointing at the root frame, and every other slot is
    /// absent.
    pub open spec fn wf(&self, root: PhysFrame<A::MinPageSize>, max_level: PageLevel) -> bool {
        &&& self.slot < PTPage::<A>::count()
        &&& forall|slot: nat|
            (#[trigger] self.entries.dom().contains(slot)) <==> slot < PTPage::<A>::count()
        &&& forall|slot: nat| #[trigger]
            self.entries.dom().contains(slot) ==> table_entry_wf::<A>(
                self.entries[slot],
                root@,
                slot,
                self.entry_vaddr(max_level, slot),
            )
        &&& self.entries[self.slot].value().is_table_spec(max_level)
        &&& self.entries[self.slot].value().page_frame_spec() == root@
        &&& forall|slot: nat| #[trigger]
            self.entries.dom().contains(slot) && slot != self.slot
                ==> !self.entries[slot].value().present_spec()
    }
}

/// A region of physical memory mapped straight through, at addresses computed
/// from the physical address alone.
///
/// The translation is a field rather than something read off the architecture:
/// where firmware parked the direct map is a choice it made, two handovers to
/// the same machine can differ, and the page table has no business being told
/// about it. What matters here is only that one exists and that the tables lie
/// under it -- one table outside and a walk of the handed-over tree stops
/// there.
#[verifier::reject_recursive_types(A)]
pub tracked struct DirectMap<A: ArchPagingMeta> {
    /// The physical addresses the firmware mapped through. A set rather than a
    /// range: firmware is free to leave several disjoint regions mapped, and
    /// nothing here needs them contiguous.
    pub ghost pa_set: Set<int>,
    /// Where a physical address appears. Any function will do: the invariants
    /// below say only that the tables are reachable through it, so an OS that
    /// establishes a `DirectMap` proves its own translation fits.
    pub ghost pa_to_va: spec_fn(usize) -> usize,
    /// The mapped frames that hold page tables, the root among them.
    pub ghost tables: Set<usize>,
    /// One permission per table entry, keyed by its frame and slot.
    pub tracked entries: Map<(usize, nat), PhysPointsTo<PTEntry<A>, A>>,
}

impl<A: ArchPagingMeta> DirectMap<A> {
    /// Whether `pa` is mapped through.
    pub open spec fn covers(&self, pa: int) -> bool {
        self.pa_set.contains(pa)
    }

    /// Whether every byte of `frame` is mapped through.
    ///
    /// Every byte, not just the ends: with no contiguity to appeal to, a table
    /// straddling a hole would be unreadable in the middle.
    pub open spec fn covers_frame(&self, frame: usize) -> bool {
        forall|off: int| 0 <= off < page_size::<A>() ==> #[trigger] self.covers(frame + off)
    }

    /// Where the direct map exposes the table in `frame`.
    pub open spec fn base(&self, frame: usize) -> usize {
        (self.pa_to_va)(frame)
    }

    /// Virtual address of entry `slot` of the table in `frame`.
    pub open spec fn entry_vaddr(&self, frame: usize, slot: nat) -> int {
        entry_vaddr_at::<A>(self.base(frame), slot)
    }

    /// The one virtual page a table page occupies.
    pub open spec fn vpage(&self, frame: usize) -> int {
        page_start_of::<A>(self.base(frame) as int)
    }

    /// Every table page is mapped through in full, and every one of its entries
    /// is well formed at the address the direct map exposes it at.
    ///
    /// The root is among them: it is a table like any other here, which is the
    /// difference from [`SelfMap`], where it is the only one.
    pub open spec fn wf(&self, root: PhysFrame<A::MinPageSize>, max_level: PageLevel) -> bool {
        &&& self.tables.contains(root@)
        &&& forall|frame: usize| #[trigger] self.tables.contains(frame) ==> self.covers_frame(frame)
        &&& forall|frame: usize, slot: nat|
            (#[trigger] self.entries.dom().contains((frame, slot))) <==> self.tables.contains(frame)
                && slot < PTPage::<A>::count()
        &&& forall|frame: usize, slot: nat| #[trigger]
            self.entries.dom().contains((frame, slot)) ==> table_entry_wf::<A>(
                self.entries[(frame, slot)],
                frame,
                slot,
                self.entry_vaddr(frame, slot),
            )
    }

    /// The virtual pages the tables occupy, which the handover can no longer
    /// hold records for.
    pub open spec fn vpages(&self) -> Set<int> {
        self.tables.map(|frame: usize| self.vpage(frame))
    }
}

/// The permissions an OS starts with: the page table the firmware left it, and
/// a pile of frames nothing can reach.
///
/// `P` is what a free frame will hold once it is mapped; [`Self::wf`] pins it to
/// exactly one frame's worth of bytes.
#[verifier::reject_recursive_types(A)]
#[verifier::accept_recursive_types(P)]
pub tracked struct InitialPermissions<A: ArchPagingMeta, P> {
    /// The frame the paging root lives in.
    pub ghost root: PhysFrame<A::MinPageSize>,
    /// Level the walk starts at.
    pub ghost max_level: PageLevel,
    /// The self map, if the firmware left one.
    pub tracked self_map: Option<SelfMap<A>>,
    /// The direct map, if the firmware left one.
    pub tracked direct_map: Option<DirectMap<A>>,
    /// One permission per frame the OS owns but cannot yet reach, keyed by the
    /// frame's physical address.
    pub tracked free_frames: Map<usize, PhysPointsTo<P, A>>,
    /// What the firmware handed over and nothing has claimed yet. The
    /// permissions above were carved from a handover; this is the remainder, and
    /// it is the only source of address tokens for anything mapped later.
    pub tracked init_toks: InitialVirtMappings<A>,
}

impl<A: ArchPagingMeta, P> InitialPermissions<A, P> {
    /// A free frame is owned, pinned, and unreachable: no virtual address
    /// translates to it, so its alias set is empty and its contents are not the
    /// OS's to assume anything about.
    pub open spec fn free_frames_wf(&self) -> bool {
        &&& vstd::layout::size_of::<P>() == page_size::<A>()
        &&& forall|pa: usize| #[trigger]
            self.free_frames.dom().contains(pa) ==> {
                let frame = self.free_frames[pa];
                // Exactly one frame's worth of memory, starting at its start:
                // `P` is a frame-sized type, so there is no offset to name and
                // no second frame to spill into.
                &&& frame.pinned_to_frame(pa)
                &&& frame.frames().len() == 1
                &&& !frame.is_pt()
                &&& frame.is_uninit()
                &&& frame.is_unmapped()
            }
            // A frame the OS may hand out is not a frame it is walking.
        &&& !self.free_frames.dom().contains(self.root@)
        &&& self.direct_map is Some ==> forall|pa: usize| #[trigger]
            self.free_frames.dom().contains(pa) ==> !self.direct_map->Some_0.tables.contains(pa)
    }

    /// The virtual pages the handover has already spent on tables.
    ///
    /// Their records live in the table entries, so [`Self::init_toks`] cannot
    /// still hold them: two claims on one page would give two permissions over
    /// one pointer.
    pub open spec fn table_vpages(&self) -> Set<int> {
        let from_self = if self.self_map is Some {
            set![self.self_map->Some_0.vpage(self.max_level)]
        } else {
            Set::empty()
        };
        let from_direct = if self.direct_map is Some {
            self.direct_map->Some_0.vpages()
        } else {
            Set::empty()
        };
        from_self.union(from_direct)
    }

    pub open spec fn wf(&self) -> bool {
        // With neither map the root is unreachable, and no walk could begin.
        &&& self.self_map is Some || self.direct_map is Some
        &&& self.self_map is Some ==> self.self_map->Some_0.wf(self.root, self.max_level)
        &&& self.direct_map is Some ==> self.direct_map->Some_0.wf(self.root, self.max_level)
        &&& self.free_frames_wf()
        &&& self.init_toks.init_wf()
        &&& forall|vpage: int| #[trigger]
            self.table_vpages().contains(vpage) ==> !self.init_toks.dom().contains(vpage)
    }
}

} // verus!

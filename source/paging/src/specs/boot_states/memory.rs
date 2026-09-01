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
//! which exposes every table that happens to lie in that region at once. A
//! handover reaches its root one way or the other -- neither, and no walk could
//! read its own root.
//!
//! # The three parts of the address space
//!
//! Every virtual address a handover leaves behind is in exactly one of three
//! parts: the self map's, whose addresses are derived from its slot; the direct
//! map's, whose addresses are derived from its physical set; and everything
//! else, which is what the OS is free to map. [`InitialPermissions::init_toks`]
//! holds records for the third part only, because the first two already have
//! permissions over them -- a record in two places would give two permissions
//! over one pointer.
//!
//! A free frame is a [`PhysPointsTo`]: pinned, so its physical address names
//! it, which is the only name it has. The difference from a mapped page is
//! entirely in `ptrs` -- that is the point of a permission carrying a *set* of
//! pointers, since the empty set is a perfectly good element of it and is
//! exactly what "not mapped" means.
use crate::entry::PTEntry;
use crate::level::PageLevel;
#[cfg(verus_only)]
use crate::specs::points_to::page_start_of;
use crate::specs::points_to::{Mapping, PhysPointsTo, VirtAddrTok};
use crate::structs::arch_contract::*;
use crate::structs::frame::PhysFrame;
use crate::structs::ptpage::PTPage;
use crate::structs::sizes::ENTRY_COUNT;
use crate::structs::sizes::{MinPageSize, PAGE_SIZE};
use crate::ArchPagingMeta;
#[cfg(verus_only)]
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
pub tracked struct InitialVirtMappings {
    /// The pages handed over. Not a range: what the firmware leaves usable need
    /// not be contiguous, so the set is the only honest description.
    pub ghost vpages: Set<int>,
    /// The virtual addresses, as one token.
    pub tracked virt: VirtAddrTok,
    /// The half of each page's record that the permissions share out, per page.
    /// A permission carved from this takes the part of it that matches the bytes
    /// it owns; see [`Mapping::share_of`].
    pub tracked records: Map<int, Mapping>,
    /// The half of each page's record the page table keeps.
    pub tracked auths: Map<int, Mapping>,
}

impl InitialVirtMappings {
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
            self.dom().contains(vpage) ==> self.records[vpage].share() == Mapping::share_of(
                PAGE_SIZE as int,
            )
        &&& forall|vpage: int| #[trigger]
            self.dom().contains(vpage) ==> self.auths[vpage].share() == Mapping::share_of(
                PAGE_SIZE as int,
            )
    }
}

/// Virtual address at which a self map installed at slot `k` exposes the root
/// table, for the levels from `level` down to the leaf.
///
/// Every index of the address is `k`, because each step of the walk re-reads
/// the self entry and lands back on the root. It is the one address a walk can
/// reach the root at when the root maps nothing else.
/// Bytes of virtual address space one slot of `level` spans.
pub open spec fn slot_region_size<A: ArchPagingMeta>(level: PageLevel) -> nat {
    pow2(level_shift(level.depth() as nat))
}

/// The starts of the pages covering `[start, end)`, whose ends are both page
/// aligned.
pub open spec fn pages_in<A: ArchPagingMeta>(start: int, end: int) -> Set<int> {
    Set::range(start / PAGE_SIZE as int, end / PAGE_SIZE as int).map(|i: int| i * PAGE_SIZE as int)
}

pub open spec fn self_map_base<A: ArchPagingMeta>(k: usize, level: PageLevel) -> nat
    decreases level.depth(),
{
    let here = k * pow2(level_shift(level.depth() as nat));
    match level.spec_child() {
        Some(child) => (here + self_map_base::<A>(k, child)) as nat,
        None => here as nat,
    }
}

/// The entries of one table page, as the type a permission over the whole page
/// carries.
///
/// One permission per page rather than one per entry: a page is what firmware
/// allocated, what a lock will later guard, and what
/// [`crate::specs::points_to::GeneralPointsTo::into_elements`] can still chop up
/// when a caller wants the entries separately.
///
/// The length is [`ENTRY_COUNT`] rather than `PTPage::<A>::NUM_ENTRIES` because
/// the latter is a generic const operation, which Rust will not accept in a type
/// outside `PTPage` itself. `level_geometry_wf` is what ties the two together.
pub type TableEntries<A> = [PTEntry<A>; ENTRY_COUNT];

/// What every table page the firmware hands over looks like: page-table memory,
/// pinned to its own frame, and reachable at exactly the one virtual address the
/// handover exposes it at.
///
/// Shared by both ways in, because the two differ only in what that address is.
/// The `forall`/`exists` pair is the whole of "exactly one alias": no alias the
/// handover does not account for, and at least one, or the page could not be
/// read at all.
pub open spec fn table_page_wf<A: ArchPagingMeta>(
    page: PhysPointsTo<TableEntries<A>>,
    frame: usize,
    vaddr: int,
) -> bool {
    &&& page.is_pt()
    &&& page.is_init()
    &&& page.pinned_to_frame(frame)
    &&& page.is_at_phys_addr(frame as int)
    &&& forall|p: *mut TableEntries<A>| #[trigger] page.covers(p) ==> p@.addr == vaddr
    &&& exists|p: *mut TableEntries<A>| #[trigger] page.covers(p)
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
    /// The root table. Pinned: the MMU walks the table by physical address, so
    /// a table page whose frame could move is not a table page.
    pub tracked table: PhysPointsTo<TableEntries<A>>,
}

impl<A: ArchPagingMeta> SelfMap<A> {
    /// Where the self map exposes the root table.
    pub open spec fn base(&self, max_level: PageLevel) -> usize {
        self_map_base::<A>(self.slot as usize, max_level) as usize
    }

    /// The one virtual page the root table occupies. The self map exposes the
    /// whole table at [`Self::base`], and a table is exactly one page.
    pub open spec fn vpage(&self, max_level: PageLevel) -> int {
        page_start_of(self.base(max_level) as int)
    }

    /// First address of the slot the self map spends.
    pub open spec fn region_start(&self, max_level: PageLevel) -> int {
        self.slot as int * slot_region_size::<A>(max_level) as int
    }

    /// One past the last.
    pub open spec fn region_end(&self, max_level: PageLevel) -> int {
        self.region_start(max_level) + slot_region_size::<A>(max_level)
    }

    /// Every page of the slot, not just the root's.
    ///
    /// A root that maps nothing but itself sends every address in the slot back
    /// through the self entry, so the whole region resolves into the root's own
    /// frame. None of it is the OS's to hand out, even though only
    /// [`Self::vpage`] is where a walk reads the table.
    pub open spec fn vpages(&self, max_level: PageLevel) -> Set<int> {
        pages_in::<A>(self.region_start(max_level), self.region_end(max_level))
    }

    /// The root table is well formed at the address the self map exposes it at,
    /// and it maps itself and nothing else: the self slot holds a table entry
    /// pointing at the root frame, and every other slot is absent.
    pub open spec fn wf(&self, root: PhysFrame<MinPageSize>, max_level: PageLevel) -> bool {
        &&& self.slot < ENTRY_COUNT
        &&& table_page_wf::<A>(self.table, root@, self.base(max_level) as int)
        &&& self.table.value()[self.slot as int].is_table_spec(max_level)
        &&& self.table.value()[self.slot as int].page_frame_spec() == root@
        &&& forall|i: int|
            0 <= i < ENTRY_COUNT && i != self.slot ==> !(
            #[trigger] self.table.value()[i]).present_spec()
    }
}

/// A region of physical memory mapped straight through, at addresses computed
/// from the physical address alone.
///
/// The translation is a field rather than something read off the architecture:
/// where firmware parked the direct map is a choice it made, two handovers to
/// the same machine can differ, and the page table has no business being told
/// about it.
///
/// A direct map need not be the way in. Firmware that left a self map may still
/// have mapped a region of ordinary memory through, and then [`Self::tables`]
/// is empty and this is just a window the OS can read. Whether the *root* is
/// reachable here is [`InitialPermissions::wf`]'s question, not this struct's.
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
    /// The table pages this map holds, keyed by frame. Empty for a direct map
    /// of ordinary memory, whose domain is then the set of no frames.
    pub tracked tables: Map<usize, PhysPointsTo<TableEntries<A>>>,
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
        forall|off: int| 0 <= off < PAGE_SIZE ==> #[trigger] self.covers(frame + off)
    }

    /// Where the direct map exposes the table in `frame`.
    pub open spec fn base(&self, frame: usize) -> usize {
        (self.pa_to_va)(frame)
    }

    /// The one virtual page a table page occupies.
    pub open spec fn vpage(&self, frame: usize) -> int {
        page_start_of(self.base(frame) as int)
    }

    /// Whichever table pages this map does hold are mapped through in full, and
    /// every one of their entries is well formed at the address the map exposes
    /// it at.
    ///
    /// Vacuous when [`Self::tables`] is empty, which is what lets a direct map
    /// of ordinary memory satisfy it. Unlike [`SelfMap`], the root gets no
    /// special treatment: here it is a table like any other, and it need not be
    /// one of these at all.
    pub open spec fn map_pts(&self) -> bool {
        forall|frame: usize| #[trigger]
            self.tables.dom().contains(frame) ==> self.covers_frame(frame) && table_page_wf::<A>(
                self.tables[frame],
                frame,
                self.base(frame) as int,
            )
    }

    /// Where a walk of the tables this map holds sends `vaddr`, starting in
    /// `frame` at `level`, or `None` if it runs off a missing entry or off a
    /// table this map does not hold.
    ///
    /// A concrete walk rather than an appeal to
    /// [`crate::specs::page_table::PageTableHandle::translates`]: there is no
    /// handle yet at handover time, and the entries are right here.
    pub open spec fn walk(&self, frame: usize, level: PageLevel, vaddr: usize) -> Option<int>
        decreases level.depth(),
    {
        let index = spec_entry_index::<A>(vaddr, level);
        if !self.tables.dom().contains(frame) {
            None
        } else {
            let entry = self.tables[frame].value()[index as int];
            if !entry.present_spec() {
                None
            } else if entry.is_table_spec(level) {
                match level.spec_child() {
                    Some(child) => self.walk(entry.page_frame_spec(), child, vaddr),
                    None => None,
                }
            } else {
                Some(
                    entry.page_frame_spec() + vaddr as nat % pow2(
                        level_shift(level.depth() as nat),
                    ),
                )
            }
        }
    }

    /// The tables are readable, and they say what this map claims: every
    /// address it covers translates, through the tree rooted at `root`, back to
    /// the physical address its own `pa_to_va` derived it from.
    ///
    /// [`Self::map_pts`] alone is a claim about permissions only -- it says the
    /// entries can be read, not that reading them leads anywhere in particular.
    /// This is what makes "mapped straight through" mean something, and it is
    /// only statable when the map holds the tables the walk needs: a direct map
    /// of ordinary memory alongside a self map cannot prove its own translation,
    /// because the tables proving it live in the self map.
    pub open spec fn wf_with_root(
        &self,
        root: PhysFrame<MinPageSize>,
        max_level: PageLevel,
    ) -> bool {
        &&& self.map_pts()
        &&& self.tables.dom().contains(root@)
        &&& forall|pa: int| #[trigger]
            self.pa_set.contains(pa) ==> self.walk(root@, max_level, (self.pa_to_va)(pa as usize))
                == Some(pa)
    }

    /// Every page the direct map exposes.
    ///
    /// The whole region, not just the tables': firmware mapped all of it, so
    /// all of it is readable and none of it is the OS's to hand out.
    pub open spec fn vpages(&self) -> Set<int> {
        self.pa_set.map(|pa: int| page_start_of((self.pa_to_va)(pa as usize) as int))
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
    pub ghost root: PhysFrame<MinPageSize>,
    /// Level the walk starts at.
    pub ghost max_level: PageLevel,
    /// The self map, if the firmware left one.
    pub tracked self_map: Option<SelfMap<A>>,
    /// The direct map, if the firmware left one.
    pub tracked direct_map: Option<DirectMap<A>>,
    /// One permission per frame the OS owns but cannot yet reach, keyed by the
    /// frame's physical address.
    pub tracked free_frames: Map<usize, PhysPointsTo<P>>,
    /// What the firmware handed over and nothing has claimed yet. The
    /// permissions above were carved from a handover; this is the remainder, and
    /// it is the only source of address tokens for anything mapped later.
    pub tracked init_toks: InitialVirtMappings,
}

impl<A: ArchPagingMeta, P> InitialPermissions<A, P> {
    /// A free frame is owned, pinned, and unreachable: no virtual address
    /// translates to it, so its alias set is empty and its contents are not the
    /// OS's to assume anything about.
    pub open spec fn free_frames_wf(&self) -> bool {
        &&& vstd::layout::size_of::<P>() == PAGE_SIZE
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
            self.free_frames.dom().contains(pa) ==> !self.direct_map->Some_0.tables.dom().contains(
                pa,
            )
    }

    /// The first of the three parts: what the self map's slot spends.
    pub open spec fn self_vpages(&self) -> Set<int> {
        if self.self_map is Some {
            self.self_map->Some_0.vpages(self.max_level)
        } else {
            Set::empty()
        }
    }

    /// The second: what the direct map's physical set spends.
    pub open spec fn direct_vpages(&self) -> Set<int> {
        if self.direct_map is Some {
            self.direct_map->Some_0.vpages()
        } else {
            Set::empty()
        }
    }

    /// Both, which is everything the handover has already spent.
    pub open spec fn mapped_vpages(&self) -> Set<int> {
        self.self_vpages().union(self.direct_vpages())
    }

    /// The root table can be read: either the self map exposes it, or it is one
    /// of the tables the direct map covers.
    ///
    /// Without this no walk could begin, and a direct map alone does not supply
    /// it -- firmware may have mapped a region through that holds no tables.
    pub open spec fn root_is_reachable(&self) -> bool {
        ||| self.self_map is Some
        ||| self.direct_map is Some && self.direct_map->Some_0.tables.dom().contains(self.root@)
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.self_map is Some ==> self.self_map->Some_0.wf(self.root, self.max_level)
        &&& self.direct_map is Some
            ==> self.direct_map->Some_0.map_pts()
        // When the direct map is the way in, it also has to translate: the walk
        // that reaches the root through it walks these very entries.
        &&& self.direct_map is Some && self.direct_map->Some_0.tables.dom().contains(self.root@)
            ==> self.direct_map->Some_0.wf_with_root(self.root, self.max_level)
        &&& self.root_is_reachable()
        &&& self.free_frames_wf()
        &&& self.init_toks.init_wf()
        // The three parts really are three: firmware that put its direct map
        // inside the self map's slot would have the two describe one page
        // twice.
        &&& self.self_vpages().disjoint(
            self.direct_vpages(),
        )
        // And what is left over is the third part, which is all the OS may map.
        &&& self.init_toks.dom().disjoint(self.mapped_vpages())
    }
}

} // verus!

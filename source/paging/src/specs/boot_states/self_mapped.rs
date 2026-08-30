//! A handover whose root page table is reached through a self map.
//!
//! Two kinds of memory, and they are opposites. The root page table is
//! *reachable and pinned*: the self map gives it a virtual address, and being a
//! table it can never move. A free frame is *owned and unreachable*: the OS has
//! it, but no virtual address translates to it yet, so nothing can read or
//! write it until a mapping is installed.
//!
//! A free frame is a [`PhysPointsTo`]: pinned, so its physical address names
//! it, which is the only name it has. The difference from a mapped page is
//! entirely in `ptrs` -- that is the point of a permission carrying a *set* of
//! pointers, since the empty set is a perfectly good element of it and is
//! exactly what "not mapped" means.
use crate::entry::PTEntry;
use crate::level::PageLevel;
use crate::specs::points_to::{
    Mapping, PhysPointsTo, VirtAddrTok, page_start_of,
};
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

/// The permissions an OS starts with: one root page table that maps only
/// itself, and a pile of frames nothing can reach.
///
/// `P` is what a free frame will hold once it is mapped; [`Self::wf`] pins it to
/// exactly one frame's worth of bytes.
#[verifier::reject_recursive_types(A)]
#[verifier::accept_recursive_types(P)]
pub tracked struct InitialPermissions<A: ArchPagingMeta, P> {
    /// The frame the paging root lives in.
    pub ghost root: PhysFrame<A::MinPageSize>,
    /// Slot of the root table that points back at the root.
    pub ghost self_slot: nat,
    /// Level the walk starts at.
    pub ghost max_level: PageLevel,
    /// One permission per word of the root table, keyed by slot. Pinned: the
    /// MMU walks the table by physical address, so a table page whose frame
    /// could move is not a table page.
    pub tracked self_mapped_root_pt: Map<nat, PhysPointsTo<PTEntry<A>, A>>,
    /// One permission per frame the OS owns but cannot yet reach, keyed by the
    /// frame's physical address.
    pub tracked free_frames: Map<usize, PhysPointsTo<P, A>>,
    /// What the firmware handed over and nothing has claimed yet. The
    /// permissions above were carved from a handover; this is the remainder, and
    /// it is the only source of address tokens for anything mapped later.
    pub tracked init_toks: InitialVirtMappings<A>,
}

impl<A: ArchPagingMeta, P> InitialPermissions<A, P> {
    /// Virtual address of the root table's word `slot`, as the self map exposes
    /// it.
    pub open spec fn word_vaddr(&self, slot: nat) -> int {
        slot_addr::<A>(
            self_map_base::<A>(self.self_slot as usize, self.max_level) as usize,
            slot as int,
        )
    }

    /// The one virtual page the root table occupies.
    ///
    /// Every word of the table shares it: the self map exposes the whole table
    /// at [`self_map_base`], and a table is exactly one page, so the slot only
    /// picks an offset within this page.
    pub open spec fn vpage_of_self_mapped_root_pt(&self) -> int {
        page_start_of::<A>(self_map_base::<A>(self.self_slot as usize, self.max_level) as int)
    }

    /// Physical address of the root table's word `slot`.
    pub open spec fn word_paddr(&self, slot: nat) -> int {
        slot_addr::<A>(self.root@, slot as int)
    }

    /// Every word of the root table is a page-table word, pinned to the root
    /// frame at its own slot, and reachable at exactly one virtual address --
    /// the one the self map computes.
    pub open spec fn self_mapped_root_pt_wf(&self) -> bool {
        &&& forall|slot: nat|
            (#[trigger] self.self_mapped_root_pt.dom().contains(slot)) <==> slot
                < PTPage::<A>::count()
        &&& forall|slot: nat| #[trigger]
            self.self_mapped_root_pt.dom().contains(slot) ==> {
                let word = self.self_mapped_root_pt[slot];
                &&& word.is_pt()
                &&& word.is_init()
                &&& word.pinned_to_frame(self.root@)
                &&& word.is_at_phys_addr(self.word_paddr(slot))
                // No alias the self map does not account for.
                &&& forall|p: *mut PTEntry<A>| #[trigger]
                    word.covers(p) ==> p@.addr == self.word_vaddr(slot)
                &&& exists|p: *mut PTEntry<A>| #[trigger] word.covers(p)
            }
    }

    /// The root maps itself and nothing else: the self slot holds a table entry
    /// pointing at the root frame, and every other slot is absent.
    pub open spec fn self_map_wf(&self) -> bool {
        &&& self.self_slot < PTPage::<A>::count()
        &&& self.self_mapped_root_pt[self.self_slot].value().is_table_spec(self.max_level)
        &&& self.self_mapped_root_pt[self.self_slot].value().page_frame_spec() == self.root@
        &&& forall|slot: nat| #[trigger]
            self.self_mapped_root_pt.dom().contains(slot) && slot != self.self_slot
                ==> !self.self_mapped_root_pt[slot].value().present_spec()
    }

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
        // A frame the OS may hand out is not the frame it is walking.
        &&& !self.free_frames.dom().contains(self.root@)
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.self_mapped_root_pt_wf()
        &&& self.self_map_wf()
        &&& self.free_frames_wf()
        &&& self.init_toks.init_wf()
        // The root table's page is already carved out: its words hold the
        // records for that page, so the handover cannot still hold them too.
        &&& !self.init_toks.dom().contains(self.vpage_of_self_mapped_root_pt())
    }
}

} // verus!

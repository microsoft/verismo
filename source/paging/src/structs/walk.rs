//! Walking a page table without holding any lock.
//!
//! One recursive function serves every level. The level is a *value* carried
//! down the recursion, so there is no macro-generated family of per-level
//! walkers, and the recursion terminates because the level strictly decreases.
//!
//! Nothing here takes a lock. A slot is read through `concurrent_rw`, which
//! gives a reader an *observation* rather than the current value: what it says
//! about a slot holding a table pointer stays true (`entry_step`), and what it
//! says about anything else may already be stale. That is the honest reading of
//! a lock-free walk, and it is enough for a walk that only wants to find where
//! an address is mapped.
use concurrent_rw::RWWithPublishPayloadContract;
use vstd::prelude::*;
use vstd::raw_ptr::with_exposed_provenance;

use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{
    level_geometry_wf, slot_addr, spec_entry_index, ArchPagingMeta,
};
use crate::structs::concurrent_pt::{entry_ptr, PTPageSharedPerm};
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingHandler;

verus! {

/// Where a walk came to rest: the entry it stopped at, and enough about the
/// page holding it to go back and update it.
///
/// `base` and `index` are what an update needs -- the page's lock is looked up
/// by address, and the slot is written by index -- and `level` is what says
/// how large a page the entry maps.
pub struct WalkResult<A: ArchPagingMeta> {
    pub level: PageLevel,
    pub base: VirtAddr,
    pub index: usize,
    pub entry: PTEntry<A>,
}

/// Follows `vaddr` down from the page at `base`, stopping at the first entry
/// that is not a table pointer, or at the leaf level.
///
/// The level is a parameter rather than a property read off the page's tokens:
/// it is grounded at the root by the handle and decreases by one per step, so
/// it both bounds the recursion and is what stops the walk from reading bit 7
/// of a leaf entry as "points at a table" -- at level 0 the hardware reads that
/// bit as PAT.
pub fn walk<A: ArchPagingMeta, P: PagingHandler>(
    base: VirtAddr,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> (ret: WalkResult<A>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == base@,
    ensures
        ret.level.spec_depth() <= level.spec_depth(),
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        // Stopping on a table pointer is only allowed where descending is not:
        // at the leaf, where the bit that looks like PS is PAT.
        ret.entry.is_table_spec() ==> ret.level.spec_is_leaf(),
    decreases level.spec_depth(),
{
    let index = entry_index::<A>(vaddr, level);
    let ghost i = index as int;
    let ptr = entry_ptr::<A>(base, index, Tracked(page));
    let tracked slot = page.slots.tracked_borrow(i);
    let (entry, Tracked(_observed), Tracked(ticket)) = PTEntry::read_published(
        ptr,
        Tracked(slot),
        Tracked(None),
    );
    let stop = WalkResult { level, base, index, entry };
    if !entry.is_table() {
        return stop;
    }
    match level.child() {
        None => stop,
        Some(child_level) => {
            let tracked slot_ticket;
            let tracked child_page;
            proof {
                // `is_table` is `has_published_payload`, so the read promised a
                // ticket, and the ticket names the child page's tokens. The
                // ticket outlives this frame, which is what lets the child's
                // readers be borrowed outside any invariant block.
                slot_ticket = ticket.tracked_unwrap();
                child_page = slot.borrow_published_payload(&slot_ticket).tracked_borrow();
            }
            proof {
                lemma_phys_addr_from_bits(entry.page_frame_spec());
            }
            let child_base = P::paddr_to_vaddr::<A>(PhysAddr::from(entry.page_frame()));
            walk::<A, P>(child_base, child_level, Tracked(child_page), vaddr)
        },
    }
}

} // verus!

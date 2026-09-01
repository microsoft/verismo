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

#[cfg(verus_only)]
use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
#[cfg(verus_only)]
use crate::structs::arch_contract::{level_geometry_wf, slot_addr, spec_entry_index};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::OSPagingContract;
use crate::structs::ptpage::{entry_ptr, page_from_vaddr, PTPage};

verus! {

/// Where a walk came to rest: the entry it stopped at, and enough about the
/// page holding it to go back and update it.
///
/// `page_ptr` and `index` are what an update needs -- the page's lock is looked
/// up by the page, and the slot is written by index -- and `level` is what says
/// how large a page the entry maps.
pub struct WalkResult<A: ArchPagingMeta> {
    pub level: PageLevel,
    pub page_ptr: *mut PTPage<A>,
    pub index: usize,
    pub entry: PTEntry<A>,
}

/// Follows `vaddr` down from `page_ptr`, stopping at the first entry
/// that is not a table pointer, or at the leaf level.
///
/// The level is a parameter rather than a property read off the page's tokens:
/// it is grounded at the root by the handle and decreases by one per step, so
/// it both bounds the recursion and is what stops the walk from reading bit 7
/// of a leaf entry as "points at a table" -- at level 0 the hardware reads that
/// bit as PAT.
pub fn walk<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
) -> (ret: WalkResult<A>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
    ensures
        ret.level.depth() as nat <= level.depth() as nat,
        ret.index == spec_entry_index::<A>(vaddr@, ret.level),
        // Stopping on a table pointer is only allowed where descending is not:
        // at the leaf, where the bit that looks like PS is PAT.
        ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec(),
    decreases level.depth() as nat,
{
    let index = entry_index::<A>(vaddr, level);
    let ghost i = index as int;
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked slot = page.slots.tracked_borrow(i);
    let (entry, Tracked(_observed), Tracked(ticket)) = PTEntry::read_published(
        ptr,
        Tracked(slot),
        Tracked(None),
        Tracked(&()),
    );
    let stop = WalkResult { level, page_ptr, index, entry };
    if !entry.is_table(level) || !entry.escrows() {
        assert(entry.is_table_spec(level) ==> !entry.escrows_spec());
        return stop;
    }
    match level.child() {
        None => {
            proof {
                PageLevel::lemma_no_child_is_leaf(level);
            }
            assert(!entry.is_table_spec(level));
            stop
        },
        Some(child_level) => {
            proof {
                PageLevel::lemma_child_decreases(level);
            }
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
            let child_base = P::paddr_to_vaddr(PhysAddr::from(entry.page_frame()));
            let child_ptr = page_from_vaddr::<A>(child_base, Tracked(child_page));
            let ret = walk::<A, P>(child_ptr, child_level, Tracked(child_page), vaddr);
            assert(ret.entry.is_table_spec(ret.level) ==> !ret.entry.escrows_spec());
            ret
        },
    }
}

} // verus!

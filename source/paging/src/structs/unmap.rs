//! Changing a mapping that is already there.
//!
//! Unmapping and reprotecting differ only in what they leave behind, so they
//! are one recursive walk parameterised by a [`LeafUpdate`]. Neither allocates,
//! neither frees, and neither touches an interior table: reclaiming a table
//! page needs the outer level of exclusion, and lives on the handle.
//!
//! The walk stops at the first entry that is not a table pointer, wherever
//! that is -- a mapping installed as a huge page is found at the level it was
//! installed at, without the caller having to say so.
use concurrent_rw::RWWithPublishPayloadContract;
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
#[cfg(verus_only)]
use crate::structs::arch_contract::level_geometry_wf;
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{OSPagingContract, PageLock, PagingError};
use crate::structs::ptpage::{entry_ptr, page_from_vaddr, PTPage};

use crate::structs::update::replace_leaf_slot;

verus! {

/// What to leave in the slot of a mapping that was found.
pub enum LeafUpdate<A: ArchPagingMeta> {
    /// Clear the entry: after this the address does not map.
    Clear,
    /// Keep the frame, replace the permissions.
    SetFlags(A::PTFlags),
    /// Keep the frame and the permissions, and move the page between private
    /// and shared memory by retagging its address.
    SetSharing { shared: bool },
}

/// Applies `update` to the entry `vaddr` leads to, and returns the entry that
/// was there.
///
/// Only the page holding that entry is locked, and only for the store itself.
/// The value the walk sees on the way down may be stale, but a stale table
/// pointer is still a table pointer, and the entry that is finally replaced is
/// read again under the writer, so what comes back is what was really there.
pub fn update_leaf_at<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
    update: LeafUpdate<A>,
) -> (ret: Result<PTEntry<A>, PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
    ensures
        ret matches Ok(old) ==> !old.escrows_spec(),
    decreases level.depth() as nat,
{
    let index = entry_index::<A>(vaddr, level);
    let ghost i = index as int;
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked slot = page.slots.tracked_borrow(i);
    let (current, Tracked(_observed), Tracked(ticket)) = PTEntry::<A>::read_published(
        ptr,
        Tracked(slot),
        Tracked(None),
        Tracked(&()),
    );
    if current.escrows() {
        let child_level = match level.child() {
            None => {
                return Err(PagingError::NotMapped);
            },
            Some(child_level) => child_level,
        };
        proof {
            PageLevel::lemma_child_decreases(level);
        }
        let tracked slot_ticket;
        let tracked child_page;
        proof {
            slot_ticket = ticket.tracked_unwrap();
            child_page = slot.borrow_published_payload(&slot_ticket).tracked_borrow();
            lemma_phys_addr_from_bits(current.page_frame_spec());
        }
        let child_base = P::paddr_to_vaddr(PhysAddr::from(current.page_frame()));
        let child_ptr = page_from_vaddr::<A>(child_base, Tracked(child_page));
        return update_leaf_at::<A, P>(child_ptr, child_level, Tracked(child_page), vaddr, update);
    }
    if !current.present() {
        return Err(PagingError::NotMapped);
    }
    let replacement = leaf_replacement::<A>(current, update);
    let lock = P::page_lock(page_ptr);
    let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
    let ret = replace_leaf_slot::<A>(
        page_ptr,
        index,
        Tracked(page),
        Tracked(&mut writers),
        replacement,
    );
    lock.unlock::<A>(Tracked(page), Tracked(writers));
    ret
}

/// The entry an update leaves behind, given the one the walk found.
///
/// The frame is carried over untouched, tag bits and all: a reprotect must not
/// silently move a mapping between private and shared memory.
fn leaf_replacement<A: ArchPagingMeta>(current: PTEntry<A>, update: LeafUpdate<A>) -> (ret: PTEntry<
    A,
>)
    ensures
        !ret.escrows_spec(),
{
    match update {
        LeafUpdate::Clear => PTEntry::<A>::empty(),
        LeafUpdate::SetFlags(flags) => {
            let addr = current.paddr_field();
            proof {
                let am = A::spec_address_mask();
                let v = current.view();
                lemma_phys_addr_from_bits(v & am);
                assert((v & am) & !am == 0) by (bit_vector);
            }
            PTEntry::<A>::new_leaf(PhysAddr::from(addr), flags)
        },
        LeafUpdate::SetSharing { shared } => {
            let untagged = current.paddr_field() & !A::private_pte_mask() & !A::shared_pte_mask();
            let tag = if shared {
                A::shared_pte_mask()
            } else {
                A::private_pte_mask()
            };
            let flags = current.flags();
            proof {
                A::lemma_pte_masks_wf();
                let am = A::spec_address_mask();
                let pm = A::spec_private_mask();
                let sm = A::spec_shared_mask();
                let v = current.view();
                lemma_phys_addr_from_bits((v & am) & !pm & !sm | tag);
                assert((tag == pm || tag == sm) && pm & !am == 0 && sm & !am == 0 ==> ((v & am)
                    & !pm & !sm | tag) & !am == 0) by (bit_vector);
            }
            PTEntry::<A>::new_leaf(PhysAddr::from(untagged | tag), flags)
        },
    }
}

} // verus!

//! Installing a mapping, growing the tree where it has to.
//!
//! One recursive function again, with the level as a value. It takes no lock
//! while descending -- only the page it is about to write is locked, and only
//! for the one store -- so two threads mapping addresses that diverge high in
//! the tree never meet.
//!
//! Growing the tree is the interesting half. A new table page is built, filled
//! with zeroes by the allocator, and its writers are put into its own lock
//! *before* it is linked: after the link any walker can reach it, so by then
//! its writers must already be where every thread looks for them. Linking then
//! publishes the page's readers along with the entry, which is what lets the
//! very next step of this recursion -- and every later walk -- borrow them out
//! of the slot instead of being handed them.
use concurrent_rw::{PayloadTicket, RWWithPublishPayloadContract};
use vstd::prelude::*;

use crate::structs::address::lemma_phys_addr_from_bits;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{level_geometry_wf, ArchPagingMeta, GenericPageTableFlags};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::geometry::entry_index;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{PageLock, PagingError, OSPagingContract};
use crate::structs::ptpage::{entry_ptr, page_from_vaddr, PTPage};

use crate::structs::update::{link_table_slot, set_leaf_slot};

verus! {

/// Installs `entry` at the slot of `vaddr` in the level `target`, creating the
/// tables between `level` and `target` if they are missing.
///
/// Fails rather than replacing anything: an address that already maps must be
/// unmapped first, so that whoever owns the old mapping learns that it is
/// gone. Fails too if `target` is deeper than the tree, which is the only way
/// a caller can ask for a page size the architecture does not have here.
pub fn map_at<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
    target: PageLevel,
    entry: PTEntry<A>,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
        !entry.is_table_spec(),
    decreases level.spec_depth(), 1nat,
{
    let index = entry_index::<A>(vaddr, level);
    let ghost i = index as int;
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    if level.depth() == target.depth() {
        let lock = P::page_lock(page_ptr);
        let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
        let ret = set_leaf_slot::<A>(page_ptr, index, Tracked(page), Tracked(&mut writers), entry);
        lock.unlock::<A>(Tracked(page), Tracked(writers));
        return ret;
    }
    let child_level = match level.child() {
        None => {
            return Err(PagingError::InvalidLevel);
        },
        Some(child_level) => child_level,
    };
    let tracked slot = page.slots.tracked_borrow(i);
    let (current, Tracked(_observed), Tracked(ticket)) = PTEntry::<A>::read_published(
        ptr,
        Tracked(slot),
        Tracked(None),
    );
    if current.is_table() {
        let tracked slot_ticket;
        let tracked child_page;
        proof {
            slot_ticket = ticket.tracked_unwrap();
            child_page = slot.borrow_published_payload(&slot_ticket).tracked_borrow();
            lemma_phys_addr_from_bits(current.page_frame_spec());
        }
        let child_base = P::paddr_to_vaddr(PhysAddr::from(current.page_frame()));
        let child_ptr = page_from_vaddr::<A>(child_base, Tracked(child_page));
        return map_at::<A, P>(child_ptr, child_level, Tracked(child_page), vaddr, target, entry);
    }
    if current.present() {
        return Err(PagingError::EntryAlreadyPresent);
    }
    grow_and_map::<A, P>(page_ptr, index, level, Tracked(page), vaddr, target, entry)
}

/// Puts a new table page under the empty slot `index` and continues the map in
/// it.
///
/// Split out of [`map_at`] only to keep that function's shape readable; it is
/// one step of the same recursion and calls back into it.
fn grow_and_map<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    level: PageLevel,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    vaddr: VirtAddr,
    target: PageLevel,
    entry: PTEntry<A>,
) -> (ret: Result<(), PagingError>)
    requires
        level_geometry_wf::<A>(),
        page.wf(),
        page.base == page_ptr@.addr,
        index < PTEntry::<A>::count_per_page(),
        level.spec_child() is Some,
        !entry.is_table_spec(),
    decreases level.spec_depth(), 0nat,
{
    let child_level = match level.child() {
        None => {
            return Err(PagingError::InvalidLevel);
        },
        Some(child_level) => child_level,
    };
    let (child_ptr, ticket) = match create_and_link_child::<A, P>(
        page_ptr,
        index,
        Tracked(page),
        child_level,
    ) {
        Err(e) => {
            return Err(e);
        },
        Ok(linked) => linked,
    };
    let tracked slot = page.slots.tracked_borrow(index as int);
    let tracked child_page = slot.borrow_published_payload(ticket.borrow()).tracked_borrow();
    map_at::<A, P>(child_ptr, child_level, Tracked(child_page), vaddr, target, entry)
}

/// Allocates a table page, publishes it, and links it into the empty slot
/// `index`.
///
/// The ticket that comes back names the child's reader tokens, so the caller
/// borrows them out of the slot rather than being handed them: the same route
/// every later walk takes, and the only one that stays valid once other threads
/// can see the entry.
///
/// The writers go into the child's own lock before the link, because after the
/// link the page is reachable and whoever wants to write it will look there.
pub fn create_and_link_child<A: ArchPagingMeta, P: OSPagingContract<A>>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    child_level: PageLevel,
) -> (ret: Result<
    (*mut PTPage<A>, Tracked<PayloadTicket<Option<PTPageSharedPerm<A>>>>),
    PagingError,
>)
    requires
        page.wf(),
        page.base == page_ptr@.addr,
        index < PTEntry::<A>::count_per_page(),
    ensures
        ret matches Ok((child_ptr, ticket)) ==> {
            &&& ticket@.id() == page.slots[index as int].slot_id()
            &&& ticket@.version() == page.slots[index as int].slot_version()
            &&& ticket@.payload() is Some
            &&& ticket@.payload()->Some_0.wf()
            &&& ticket@.payload()->Some_0.base == child_ptr@.addr
        },
{
    let (paddr, Tracked(init)) = match P::allocate_table_page() {
        Err(e) => {
            return Err(e);
        },
        Ok(allocated) => allocated,
    };
    let child_base = P::paddr_to_vaddr(paddr);
    let tracked child_page;
    let tracked child_writers;
    proof {
        A::lemma_pte_masks_wf();
        let tracked (readers, writers) = init.into_page(paddr@, child_level);
        child_page = readers;
        child_writers = writers;
    }
    let child_ptr = page_from_vaddr::<A>(child_base, Tracked(&child_page));
    let child_lock = P::page_lock(child_ptr);
    child_lock.deposit::<A>(Tracked(&child_page), Tracked(child_writers));

    let tagged = PhysAddr::from(paddr.bits() | A::private_pte_mask());
    proof {
        let am = A::spec_address_mask();
        let pm = A::spec_private_mask();
        let p = paddr@;
        lemma_phys_addr_from_bits(p | pm);
        assert((p & !am == 0 && pm & !am == 0) ==> (p | pm) & !am == 0) by (bit_vector);
        assert((p & pm == 0) ==> (p | pm) & !pm == p) by (bit_vector);
    }
    let table_entry = PTEntry::<A>::new_table(tagged, A::PTFlags::parent_flags());

    let lock = P::page_lock(page_ptr);
    let Tracked(mut writers) = lock.lock::<A>(Tracked(page));
    let linked = link_table_slot::<A>(
        page_ptr,
        index,
        Tracked(page),
        Tracked(&mut writers),
        table_entry,
        Tracked(child_page),
    );
    lock.unlock::<A>(Tracked(page), Tracked(writers));
    match linked {
        Err(e) => Err(e),
        Ok(ticket) => Ok((child_ptr, ticket)),
    }
}

} // verus!

//! Updating one slot of a table page.
//!
//! Both operations take the page's writers, which come from the page's lock:
//! this is the inner of the two levels of exclusion, so two threads updating
//! different pages never contend. Neither touches the shape of the tree above
//! the page, which is what the outer level guards.
//!
//! Both refuse to overwrite a present entry. A page-table update that silently
//! replaced a live mapping would leak whatever the old entry pointed at -- for
//! a table entry, a whole subtree along with the tokens escrowed in it.
use concurrent_rw::{PayloadTicket, RWContract, RWWithPublishPayloadContract, WithPayload};
use vstd::prelude::*;

use crate::structs::arch_contract::ArchPagingMeta;
#[cfg(verus_only)]
use crate::structs::concurrent_pt::lemma_ids_match;
use crate::structs::concurrent_pt::{PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::os_contract::PagingError;
use crate::structs::ptpage::{entry_ptr, PTPage};

verus! {

/// Writes a mapping into an empty slot.
///
/// `entry` must not be a table pointer: an entry that escrows a page has to be
/// installed with the page's tokens, which is [`link_table_slot`].
pub fn set_leaf_slot<A: ArchPagingMeta>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    entry: PTEntry<A>,
) -> (ret: Result<(), PagingError>)
    requires
        page.wf(),
        page.base == page_ptr@.addr,
        old(writers).ids() =~= page.ids(),
        index < PTPage::<A>::count(),
        !entry.escrows_spec(),
    ensures
        final(writers).ids() =~= page.ids(),
        ret is Ok ==> final(writers).slots[index as int]@ == entry,
{
    let ghost i = index as int;
    proof {
        lemma_ids_match::<A>(*writers, *page);
    }
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked reader = page.slots.tracked_borrow(i);
    let current = read_slot_exact::<A>(ptr, Tracked(reader), Tracked(writers), index);
    if current.present() || current.escrows() {
        return Err(PagingError::EntryAlreadyPresent);
    }
    let ghost before = *writers;
    let tracked writer = writers.slots.tracked_borrow_mut(i);
    let Tracked(_observed) = PTEntry::write(
        ptr,
        entry,
        Tracked(reader),
        Tracked(writer),
        Tracked(&()),
    );
    proof {
        lemma_ids_unchanged::<A>(before, *writers, i);
    }
    Ok(())
}

/// Links a page this crate has just built into an empty slot, publishing its
/// tokens with it.
///
/// After this the child is reachable by every walker, and its writers are
/// reachable only through its lock -- which is why the caller deposits them
/// there and not here.
pub fn link_table_slot<A: ArchPagingMeta>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    entry: PTEntry<A>,
    Tracked(child): Tracked<PTPageSharedPerm<A>>,
) -> (ret: Result<Tracked<PayloadTicket<Option<PTPageSharedPerm<A>>>>, PagingError>)
    requires
        page.wf(),
        page.base == page_ptr@.addr,
        old(writers).ids() =~= page.ids(),
        index < PTPage::<A>::count(),
        entry.escrows_spec(),
        child.wf(),
        child.base == A::spec_paddr_to_vaddr(entry.page_frame_spec()),
    ensures
        final(writers).ids() =~= page.ids(),
        ret matches Ok(ticket) ==> {
            &&& ticket@.id() == page.slots[index as int].slot_id()
            &&& ticket@.version() == page.slots[index as int].slot_version()
            &&& entry.wf_payload(ticket@.payload())
        },
{
    let ghost i = index as int;
    proof {
        lemma_ids_match::<A>(*writers, *page);
    }
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked reader = page.slots.tracked_borrow(i);
    let current = read_slot_exact::<A>(ptr, Tracked(reader), Tracked(writers), index);
    if current.present() || current.escrows() {
        return Err(PagingError::EntryAlreadyPresent);
    }
    let ghost before = *writers;
    let tracked writer = writers.slots.tracked_borrow_mut(i);
    let (Tracked(_observed), Tracked(ticket)) = PTEntry::write_with_published_payload(
        ptr,
        entry,
        Tracked(reader),
        Tracked(writer),
        Tracked(Some(child)),
        Tracked(&()),
    );
    proof {
        lemma_ids_unchanged::<A>(before, *writers, i);
    }
    Ok(Tracked(ticket))
}

/// Replaces a slot that does not point at a table, returning what it held.
///
/// This is the one update that overwrites: unmapping and reprotecting both
/// need it. It refuses a table pointer, because dropping one would strand
/// everything below it along with the tokens escrowed in the slot.
pub fn replace_leaf_slot<A: ArchPagingMeta>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    entry: PTEntry<A>,
) -> (ret: Result<PTEntry<A>, PagingError>)
    requires
        page.wf(),
        page.base == page_ptr@.addr,
        old(writers).ids() =~= page.ids(),
        index < PTPage::<A>::count(),
        !entry.escrows_spec(),
    ensures
        final(writers).ids() =~= page.ids(),
        ret matches Ok(old) ==> !old.escrows_spec(),
        ret matches Ok(prev) ==> prev == old(writers).slots[index as int]@,
        ret is Ok ==> final(writers).slots[index as int]@ == entry,
{
    let ghost i = index as int;
    proof {
        lemma_ids_match::<A>(*writers, *page);
    }
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked reader = page.slots.tracked_borrow(i);
    let current = read_slot_exact::<A>(ptr, Tracked(reader), Tracked(writers), index);
    if current.escrows() {
        return Err(PagingError::NotLeafEntry);
    }
    let ghost before = *writers;
    let tracked writer = writers.slots.tracked_borrow_mut(i);
    let Tracked(_observed) = PTEntry::write(
        ptr,
        entry,
        Tracked(reader),
        Tracked(writer),
        Tracked(&()),
    );
    proof {
        lemma_ids_unchanged::<A>(before, *writers, i);
    }
    Ok(current)
}

/// Replaces a live mapping with a pointer at the table that reproduces it,
/// publishing that table's tokens with the entry.
///
/// This is the one update that overwrites a *present* entry, and it is sound
/// only because the caller has already built the child to cover exactly what
/// the old entry covered: the translation of every address in it is unchanged,
/// so no thread can observe the moment of the swap. What comes back is the
/// entry that was replaced, which the caller needs in order to know what it
/// promised to reproduce.
pub fn split_leaf_slot<A: ArchPagingMeta>(
    page_ptr: *mut PTPage<A>,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
    Tracked(writers): Tracked<&mut PTPageWritePerm<A>>,
    entry: PTEntry<A>,
    Tracked(child): Tracked<PTPageSharedPerm<A>>,
) -> (ret: Result<Tracked<PayloadTicket<Option<PTPageSharedPerm<A>>>>, PagingError>)
    requires
        page.wf(),
        page.base == page_ptr@.addr,
        old(writers).ids() =~= page.ids(),
        index < PTPage::<A>::count(),
        entry.escrows_spec(),
        child.wf(),
        child.base == A::spec_paddr_to_vaddr(entry.page_frame_spec()),
    ensures
        final(writers).ids() =~= page.ids(),
        ret matches Ok(ticket) ==> {
            &&& ticket@.id() == page.slots[index as int].slot_id()
            &&& ticket@.version() == page.slots[index as int].slot_version()
            &&& entry.wf_payload(ticket@.payload())
        },
{
    let ghost i = index as int;
    proof {
        lemma_ids_match::<A>(*writers, *page);
    }
    let ptr = entry_ptr::<A>(page_ptr, index, Tracked(page));
    let tracked reader = page.slots.tracked_borrow(i);
    let current = read_slot_exact::<A>(ptr, Tracked(reader), Tracked(writers), index);
    if current.escrows() {
        return Err(PagingError::NotLeafEntry);
    }
    if !current.present() {
        return Err(PagingError::NotMapped);
    }
    let ghost before = *writers;
    let tracked writer = writers.slots.tracked_borrow_mut(i);
    let (Tracked(_observed), Tracked(ticket)) = PTEntry::write_with_published_payload(
        ptr,
        entry,
        Tracked(reader),
        Tracked(writer),
        Tracked(Some(child)),
        Tracked(&()),
    );
    proof {
        lemma_ids_unchanged::<A>(before, *writers, i);
    }
    Ok(Tracked(ticket))
}

/// The value really in the slot, which only the holder of the writer can know.
///
/// A walk reads a *reachable* value; here the writers are in hand, so no store
/// can be in flight and the value is exact. That is what makes the
/// "already present" check meaningful rather than advisory.
pub fn read_slot_exact<A: ArchPagingMeta>(
    ptr: *mut usize,
    Tracked(reader): Tracked<&crate::structs::os_contract::SlotShared<A>>,
    Tracked(writers): Tracked<&PTPageWritePerm<A>>,
    index: usize,
) -> (ret: PTEntry<A>)
    requires
        reader.location() == ptr,
        index < writers.slots.len(),
        reader.id() == writers.slots[index as int].id(),
    ensures
        ret == writers.slots[index as int]@,
{
    let tracked writer = writers.slots.tracked_borrow(index as int);
    let (value, Tracked(_observed)) = PTEntry::read_exact(
        ptr,
        Tracked(reader),
        Tracked(writer),
        Tracked(&()),
    );
    value
}

/// A store leaves every writer's identity alone, so the page's writers are
/// still the writer halves of its readers and may go back to its lock.
pub proof fn lemma_ids_unchanged<A: ArchPagingMeta>(
    before: PTPageWritePerm<A>,
    after: PTPageWritePerm<A>,
    index: int,
)
    requires
        0 <= index < before.slots.len(),
        after.slots.len() == before.slots.len(),
        after.slots =~= before.slots.update(index, after.slots[index]),
        after.slots[index].id() == before.slots[index].id(),
    ensures
        after.ids() =~= before.ids(),
{
}

} // verus!

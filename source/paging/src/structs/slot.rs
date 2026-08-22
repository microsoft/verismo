//! Addressing one slot of a table page, and storing into it.
//!
//! # A trusted bridge, and why it is here
//!
//! `concurrent_rw`'s executable store operations say what value the writer
//! token ends up holding, but not that it is still the *same* token: their
//! `ensures` do not mention `final(w).id()`. The proof one layer below does --
//! `RWState::update_value` ensures `final(writer).id() == old(self).id()` --
//! but that fact is dropped on the way out.
//!
//! A page-table update cannot do without it. The writers of a page are borrowed
//! from the page's lock and have to be handed back, and what identifies them as
//! the right writers is exactly their ids. Without the clause, one store makes a
//! page's writers unreturnable.
//!
//! `concurrent_rw` is not ours to change, so the two wrappers below restate its
//! contract with that one clause added and are trusted. They are the only
//! trusted executable code in this crate. Adding the clause to
//! `concurrent_rw`'s own `ensures` would need no new proof and would let both
//! wrappers be deleted.
use concurrent_rw::{
    Observed, PayloadTicket, RWContract, RWWithPublishPayloadContract, WithPayload, WritePerm,
};
use vstd::prelude::*;
use vstd::raw_ptr::with_exposed_provenance;

use crate::structs::address::{Address, VirtAddr};
use crate::structs::arch_contract::{slot_addr, ArchPagingMeta};
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::entry::PTEntry;
use crate::structs::os_contract::SlotShared;

verus! {

/// A pointer to entry `index` of the page, with the page's provenance.
pub fn slot_ptr<A: ArchPagingMeta>(
    base: VirtAddr,
    index: usize,
    Tracked(page): Tracked<&PTPageSharedPerm<A>>,
) -> (ret: *mut usize)
    requires
        page.wf(),
        page.base == base@,
        index < PTEntry::<A>::count_per_page(),
    ensures
        ret == page.slots[index as int].ptr(),
{
    let ghost i = index as int;
    assert(page.slots[i].ptr()@.addr == slot_addr::<A>(page.base, i));
    let addr = base.bits() + index * core::mem::size_of::<usize>();
    with_exposed_provenance(addr, Tracked(page.provenance))
}

/// Stores `value`, leaving the slot's payload where it is.
///
/// Trusted; see the module comment. The contract is `RWContract::write`'s, plus
/// the writer's identity.
#[verifier::external_body]
pub fn store_slot<A: ArchPagingMeta>(
    ptr: *mut usize,
    value: PTEntry<A>,
    Tracked(r): Tracked<&SlotShared<A>>,
    Tracked(w): Tracked<&mut WritePerm<PTEntry<A>>>,
) -> (ret: Tracked<Observed<PTEntry<A>>>)
    requires
        r.ptr() == ptr,
        r.id() == old(w).id(),
        old(w).write_value_requires(value),
    ensures
        r.has_observed(ret@),
        ret@@ == value,
        value == final(w)@,
        final(w).id() == old(w).id(),
{
    PTEntry::write(ptr, value, Tracked(r), Tracked(w))
}

/// Stores `value` and publishes `payload` with it, returning the first ticket.
///
/// Trusted; see the module comment. The contract is
/// `RWContract::write_with_published_payload`'s, plus the writer's identity.
#[verifier::external_body]
pub fn store_slot_publishing<A: ArchPagingMeta>(
    ptr: *mut usize,
    value: PTEntry<A>,
    Tracked(r): Tracked<&SlotShared<A>>,
    Tracked(w): Tracked<&mut WritePerm<PTEntry<A>>>,
    Tracked(payload): Tracked<Option<PTPageSharedPerm<A>>>,
) -> (ret: (Tracked<Observed<PTEntry<A>>>, Tracked<PayloadTicket<Option<PTPageSharedPerm<A>>>>))
    requires
        r.ptr() == ptr,
        r.id() == old(w).id(),
        old(w).write_value_payload_requires(value, payload),
        value.is_table_spec(),
        !old(w)@.is_table_spec(),
    ensures
        r.has_observed(ret.0@),
        ret.0@@ == value,
        value == final(w)@,
        final(w).id() == old(w).id(),
        ret.1@.id() == r.slot_id(),
        ret.1@.version() == r.slot_version(),
        value.wf_payload(ret.1@.payload()),
{
    PTEntry::write_with_published_payload(ptr, value, Tracked(r), Tracked(w), Tracked(payload))
}

} // verus!

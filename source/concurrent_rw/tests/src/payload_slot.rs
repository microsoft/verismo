//! Round-trip proof for the selected payload-slot implementation.

#[cfg(verus_only)]
use concurrent_rw::tokens_impl::payload_slot::SlotOwner;
use vstd::prelude::*;

verus! {

/// Fill a fresh slot, hand out tickets, borrow through one, and reclaim the payload.
proof fn example_slot_round_trip<P>(tracked payload: P) {
    let tracked (owner, handle) = SlotOwner::<P>::new();
    let tracked (owner, first_ticket) = owner.put(payload);
    let tracked (owner, second_ticket) = owner.mint_ticket();
    assert(first_ticket.payload() == payload);
    assert(second_ticket.payload() == payload);

    let tracked seen = handle.borrow(&second_ticket);
    assert(seen == payload);

    let tracked (owner, handle, reclaimed) = owner.take(handle);
    assert(reclaimed == payload);
    assert(owner.version() == 1);
    assert(handle.version() == 1);
    assert(first_ticket.version() == 0);
}

} // verus!

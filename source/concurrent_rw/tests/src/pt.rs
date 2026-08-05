//! A worked client of the token library: a page-table entry.
//!
//! `PTEntry` wraps a `usize` and implements the three client traits -- [`WithPayload`],
//! [`HasAtomicType`], and [`RWModel`] -- plus [`PublishPayload`], so it stands as evidence that the
//! traits can actually be discharged, and that a client's tracked payload survives the invariant
//! block it was borrowed under. That last point is what `example_borrow_outlives_invariant`
//! demonstrates.
//!
//! `walk` is the payoff: a page-walk descent, written as an ordinary recursive function that
//! opens no invariant by hand. `pt2` is the same client with publishing turned off, and
//! it descends by hand, one nested invariant block per level -- reading the two side by side is
//! the clearest statement of what [`PublishPayload`] actually buys.
//!
//! This module lives in the test crate so the reusable library can verify independently from its
//! worked clients.
use concurrent_rw::*;
use vstd::prelude::*;
use vstd::raw_ptr::IsExposed;
#[cfg(verus_only)]
use vstd::std_specs::convert::{FromSpec, FromSpecImpl, IntoSpec};

verus! {

pub struct PTEntry {
    pub value: usize,
}

impl From<usize> for PTEntry {
    fn from(value: usize) -> Self {
        PTEntry { value }
    }
}

impl From<PTEntry> for usize {
    fn from(entry: PTEntry) -> Self {
        entry.value
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<usize> for PTEntry {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: usize) -> PTEntry {
        PTEntry { value: v }
    }
}

#[cfg(verus_only)]
impl FromSpecImpl<PTEntry> for usize {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: PTEntry) -> usize {
        v.value
    }
}

impl PTEntry {
    pub open spec fn inv(self) -> bool {
        true
    }

    pub open spec fn present_spec(&self) -> bool {
        self.value != 0
    }

    #[verifier::when_used_as_spec(present_spec)]
    pub fn present(&self) -> bool
        returns
            self.present(),
    {
        self.value != 0
    }

    pub open spec fn next_spec(&self) -> usize {
        self.value
    }

    #[verifier::when_used_as_spec(next_spec)]
    pub fn next(&self) -> usize
        returns
            self.next(),
    {
        self.value
    }
}

pub struct Extra {
    reader: Seq<Reader<PTEntry, Extra>>,
    provenance: IsExposed,
}

impl WithPayload for PTEntry {
    type Payload = Extra;

    closed spec fn wf_payload(self, payload: Self::Payload) -> bool {
        self.present() ==> {
            &&& payload.reader.len() == 512
            &&& forall|i: int|
                ((#[trigger] payload.reader[i]).ptr().addr() == self.next() + i * 8)
                    && payload.reader[i].ptr()@.provenance == payload.provenance@
        }
    }
}

impl IsValidAtomicType for PTEntry {
    type AtomicType = usize;
}

impl RWModel for PTEntry {
    // A present entry has handed its child readers out to page walkers; reading can only take it
    // to another present entry with the same child, so the payload stays valid.
    open spec fn has_published_payload(self) -> bool {
        self.present()
    }

    proof fn into_from_obeys() where Self: From<Self::AtomicType> + Into<Self::AtomicType> {
    }

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,
     {
    }

    /// Where a present entry may go: it stays present and keeps pointing at the same child table.
    ///
    /// The payload is unconstrained. This model publishes, so a reader that wants to pin a
    /// payload takes a ticket instead, and there is nothing for the relation to carry.
    open spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool {
        pair.value().present() ==> {
            &&& other.value().present()
            &&& pair.value().next() == other.value().next()
        }
    }

    proof fn reachable_self(pair: Snapshot<Self, Self::Payload>) {
    }

    proof fn reachable_transitive(
        a: Snapshot<Self, Self::Payload>,
        b: Snapshot<Self, Self::Payload>,
        c: Snapshot<Self, Self::Payload>,
    ) {
    }
}

// This model publishes payloads, so it opts into the ticket API. A present entry has handed its
// child readers out to page walkers, and reading can only take it to another present entry, so
// the one obligation follows from the relation alone.
impl PublishPayload for PTEntry {
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    ) {
    }
}

// End-to-end check: read an entry, and go on holding a reference to its payload after the atomic
// invariant block has closed. This is the thing an `AtomicInvariant` cannot do by itself.
fn example_borrow_outlives_invariant(ptr: *mut usize, Tracked(r): Tracked<&Reader<PTEntry, Extra>>)
    requires
        r.ptr() == ptr,
{
    let (value, Tracked(observed), Tracked(ticket)) = PTEntry::read_published(
        ptr,
        Tracked(r),
        Tracked(None),
    );
    if value.value != 0 {
        proof {
            let tracked ticket = ticket.tracked_unwrap();
            let tracked payload = r.borrow_published_payload(&ticket);
            // The invariant block is long gone, yet the payload is still ours to look at, and it
            // is still well formed for the value we read.
            assert(value.wf_payload(*payload));
        }
    }
}

// End-to-end check: descend a level, the published way.
//
// The counterpart is `pt2::example_read_child_entry`, which does the same walk with no ticket.
// Because the payload reference outlives the block it came from, this version never opens an
// atomic invariant by hand: `read_published` on the parent, borrow the child readers, rebuild
// the child pointer, `read` the child. No nesting, no namespace discipline, no direct atomic
// load, and no argument that two separate borrows agree. That is what the ticket buys.
fn example_read_child_entry(ptr: *mut usize, Tracked(r): Tracked<&Reader<PTEntry, Extra>>)
    requires
        r.ptr() == ptr,
{
    let (value, Tracked(observed), Tracked(ticket)) = PTEntry::read_published(
        ptr,
        Tracked(r),
        Tracked(None),
    );
    if !value.present() {
        return;
    }
    let tracked slot_ticket;
    let tracked payload;
    proof {
        // `value.present()` is `has_published_payload()`, so a ticket was promised.
        slot_ticket = ticket.tracked_unwrap();
        payload = r.borrow_published_payload(&slot_ticket);
    }
    // `IsExposed` is `Copy`, so the provenance comes straight off the borrowed payload -- no need
    // to carry it out of anywhere, because nothing was ever entered.
    let child_ptr: *mut usize = vstd::raw_ptr::with_exposed_provenance(
        value.next(),
        Tracked(payload.provenance),
    );
    let tracked next_reader = payload.reader.tracked_borrow(0);
    // And now the child is just another location this crate governs: no invariant to open by
    // hand, no direct atomic load, no permission to dig out. One level down, same operation.
    let (_child_value, Tracked(_child_observed)) = PTEntry::read(
        child_ptr,
        Tracked(next_reader),
        Tracked(None),
    );
}

/// PROPERTY 1, through the contract: a read taken while holding an `Observed` token returns a
/// value reachable from the one that token names.
fn example_read_moves_forward(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    Tracked(past): Tracked<Observed<PTEntry>>,
)
    requires
        r.ptr() == ptr,
        r.has_observed(past),
{
    let ghost was = past.snapshot();
    let (value, Tracked(now), Tracked(_ticket)) = PTEntry::read_published(
        ptr,
        Tracked(r),
        Tracked(Some(&past)),
    );
    proof {
        // Whatever a concurrent writer did, it moved us forward and not back.
        assert(PTEntry::reachable(was, now.snapshot()));
    }
}

/// PROPERTY 2b, through the contract: two readers of one slot borrow the *same* payload.
///
/// This is the reader-level corollary of `payloads_agree`, which is stated over tickets. It costs
/// one line, which is why the contract states the ticket-level form.
proof fn example_two_readers_see_one_payload(
    tracked r1: &Reader<PTEntry, Extra>,
    tracked r2: &Reader<PTEntry, Extra>,
    tracked t1: &PayloadTicket<Extra>,
    tracked t2: &PayloadTicket<Extra>,
)
    requires
        r1.slot_id() == t1.id(),
        r1.slot_version() == t1.version(),
        r2.slot_id() == t2.id(),
        r2.slot_version() == t2.version(),
        r1.slot_id() == r2.slot_id(),
        r1.slot_version() == r2.slot_version(),
{
    PTEntry::payloads_agree(t1, t2);
    let tracked p1 = r1.borrow_published_payload(t1);
    let tracked p2 = r2.borrow_published_payload(t2);
    assert(*p1 == *p2);
}

// End-to-end check: a *recursive* walk, which is the thing publishing makes possible.
//
// The unpublished counterpart cannot be written. There the child's `Reader` is borrowed out of the
// parent's invariant and dies at the closing brace, so the child must be read inside the parent's
// block. That forces one nested block per level, and Verus will not let a recursive function
// produce them: the body of `open_atomic_invariant!` must be atomic, so the recursive call would
// have to be `#[verifier::atomic]`, and that attribute is rejected on recursive functions. See
// `pt2::walk_level2` and `walk_level3`, which spell the nesting out by hand.
//
// Here `borrow_published_payload` hands back `&'s T::Payload` tied to the *ticket*, not to any
// invariant. The ticket is owned by this stack frame, so the child's `Reader` borrow lives as long
// as the frame, and the recursive call is an ordinary call at the top level. No invariant is
// opened by hand anywhere in this function.
fn walk(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<PTEntry, Extra>>,
    index: usize,
    level: usize,
) -> (ret: usize)
    requires
        r.ptr() == ptr,
        index < 512,
    decreases level,
{
    let (value, Tracked(observed), Tracked(ticket)) = PTEntry::read_published(
        ptr,
        Tracked(r),
        Tracked(None),
    );
    if level == 0 || !value.present() {
        return value.value;
    }
    let tracked slot_ticket;
    let tracked payload;
    proof {
        // `value.present()` is `has_published_payload()`, so PROPERTY 3a promised a ticket.
        slot_ticket = ticket.tracked_unwrap();
        payload = r.borrow_published_payload(&slot_ticket);
    }
    // `wf_payload` puts entry `index` of the child table at a real address, so the sum fits.
    assert(payload.reader[index as int].ptr().addr() == value.next() + index * 8);
    let child_ptr: *mut usize = vstd::raw_ptr::with_exposed_provenance(
        value.next() + index * 8,
        Tracked(payload.provenance),
    );
    let tracked next_reader = payload.reader.tracked_borrow(index as int);
    walk(child_ptr, Tracked(next_reader), index, level - 1)
}

} // verus!

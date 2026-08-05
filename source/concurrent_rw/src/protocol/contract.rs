//! **What this crate guarantees.** Read this file to find out what has been proved.
//!
//! [`crate::protocol::model`] collects what a *client* must supply; this file collects what the
//! library gives back. Nothing here has a body: [`crate::tokens_impl::contract_proof`] carries
//! the impls, so a guarantee stated here and not proved there is a compile error.
//!
//! # The trade
//!
//! A `PointsTo` is already a concurrency model -- shared xor mutable. [`RWContract::build_rw`]
//! consumes it and hands back two tokens that may be used at the same time. There is no cell
//! type here; these tokens are what replaces the `PointsTo`. Exactly one of each exists per
//! pointer -- the "multiple readers" is that a read needs only `&RWShared`, so the one token can
//! be shared across threads.
//!
//! ```text
//!              PointsTo<T>
//!                  | build_rw
//!      +--------------------------------------+
//!      v                                      v
//!      RWShared -- one, shared by &             WritePerm -- one, used by &mut
//!      |                                      |
//!      |                                      |  write
//!      | read, read_published                 |   must land the store in
//!      |   &RWShared, plus optionally           |   reachable(pair now, pair new)
//!      |   an Observed, as `past`             |
//!      v                                      |
//!      Observed --- hand to the next read ----------+--> that read returns a pair
//!      |            as its `past`                          reachable from this one
//!      |
//!      | read_published, when the value says it has published
//!      v
//!      PayloadTicket --- with &RWShared ---> &Payload, outliving the block
//!                        borrow_published_payload
//! ```
//!
//! The one `&mut` is on the `WritePerm`, and it separates writers from writers, never from readers:
//! a read and the write both take `&RWShared` and open the same invariant.
//!
//! Exclusion is not the only way to make interference harmless: it prevents interference, where
//! an ordering makes it survivable. Every store must land in `RWModel::reachable` of the pair it
//! replaces ([`WritePerm::write_value_requires`]), so a reader that has fallen behind holds a value
//! that is imprecise but never wrong. That is the trade -- overlap, bought with reads that return
//! a reachable value rather than *the* stored one. The obligation is therefore all on the write:
//! a read requires nothing but the right pointer, and [`RWContract::write`] is where the
//! properties below are paid for.
//!
//! # The three properties
//!
//! | | guarantee | stated on |
//! |---|---|---|
//! | 1 | **Reads move forward.** Once you have observed a value and the payload beside it, every later read returns a pair `reachable` from that one. | [`RWContract::read`] |
//! | 2 | **With the writer in hand, reads are exact again.** Nobody else can be storing, so you read *the* stored value. | [`RWContract::read_exact`] |
//! | 3a | **A published payload is available.** If the value you read says it published, you get a ticket. | [`RWWithPublishPayloadContract::read_published`] |
//! | 3b | **A published payload is one payload.** Two tickets at one slot and version name the *same* payload. Without this, publishing would be empty. | [`RWWithPublishPayloadContract::payloads_agree`] |
//!
//! Property 1's relation is on *pairs*, because a claim about a value alone would say nothing
//! about the payload beside it: a writer may swap the payload for any other well formed one.
//! Property 2 shows the relaxation in property 1 is exactly the price of concurrency, refunded
//! when there is none. Property 3 is opt-in: a model implements [`PublishPayload`], and one that
//! never publishes gets 1 and 2 and nothing else.
//!
//! # Whether to publish
//!
//! Any thread can reach an *un*published payload -- a reader opens the same invariant the writer
//! does. The question is *where you may use it*: unpublished, only inside that block, which
//! admits one atomic operation and ghost code. Publishing lets the borrow escape, so ordinary
//! code can run with the payload in hand. That is a difference in what you can *say*: publishing
//! binds the value to a particular payload, so two blocks get the same one.
//!
//! Both examples descend one page-table level, and show the cost:
//!
//! | | `concurrent_rw_tests::pt` -- publishes | `concurrent_rw_tests::pt2` -- does not |
//! |---|---|---|
//! | the payload reference | outlives the block it came from | dies at the closing brace |
//! | the walk | an ordinary recursive function, opening no invariant by hand | one nested block per level, written out |
//! | reading a child | the library's own `read` | a raw atomic load, which is all a block body accepts |
//! | namespaces | not the client's problem | one `distinct_namespace` per pair held open |
//! | what crosses the brace | the payload itself | only what `reachable` promised about the pair |
//!
//! `pt2` pays in shape, not in soundness: its `reachable` pins a present entry's provenance,
//! which is what lets a pointer built in one block still be the child's pointer in the next.
//!
//! Publishing does not freeze the payload's contents, only which payload the value is bound to.
//! It is one-way while the `RWShared` stays whole: `PayloadHolder::reclaim` must consume the
//! reader's `SlotHandle`, and nothing in [`crate::tokens_impl`] surrenders that handle yet. What
//! holds unconditionally is [`PublishPayload::payload_stays_published`]: no value reachable by
//! *reading* ever un-publishes, so a concurrent write cannot undercut a ticket you hold.
use crate::tokens_impl::payload_slot::PayloadTicket;
use crate::tokens_impl::{Observed, PublishPayload, RWModel, RWShared, WritePerm};
#[cfg(verus_only)]
use vstd::invariant::OpenInvariantCredit;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::raw_ptr::PointsTo;
#[cfg(verus_only)]
use vstd::std_specs::convert::{FromSpec, FromSpecImpl, IntoSpec};

verus! {

/// The guarantees `mrsw_tokens_v2` offers a client that has implemented [`RWModel`].
pub trait RWContract: RWModel + From<Self::AtomicType> + Into<Self::AtomicType> {
    /// Trades a `PointsTo` for an initialised location for MRSW access to it.
    ///
    /// Consumes the `PointsTo`, under which a read may never run during a write, and returns a
    /// `RWShared` and a `WritePerm` in its place. From here on reads and the write may overlap freely:
    /// any number of readers may read while the single writer is writing. The price is that no
    /// read afterwards returns *the* stored value, only a reachable one -- see [`Self::read`].
    ///
    /// The third token is an `Observed` for the value stored at the moment of the trade. Whoever
    /// gives the `PointsTo` up knows what was in it, so this is where the first one comes from;
    /// every later read is a [`Self::read`] from one you already hold.
    proof fn build_rw(
        value: Self,
        tracked points_to: PointsTo<Self::AtomicType>,
        tracked payload: Self::Payload,
    ) -> (tracked ret: (RWShared<Self, Self::Payload>, WritePerm<Self>, Observed<Self>))
        requires
            points_to.is_init(),
            points_to.value().into_spec() === value,
            value.wf_payload(payload),
            !value.has_published_payload(),
        ensures
            ret.0.ptr() == points_to.ptr(),
            ret.0.id() == ret.1.id(),
            ret.2@ == value,  // names the value stored at the hand-over
            ret.0.has_observed(ret.2),
    ;

    /// Reverses [`Self::build_rw`], recovering exclusive ownership of the location and payload.
    ///
    /// Consuming the `RWShared` proves no reader can open the invariant again. If the payload was
    /// published, teardown reclaims it and advances the slot version, so tickets that remain in
    /// ghost state no longer grant a borrow. The returned permission contains the value named by
    /// the consumed writer token.
    proof fn teardown_rw(
        tracked r: RWShared<Self, Self::Payload>,
        tracked w: WritePerm<Self>,
    ) -> (tracked ret: (PointsTo<Self::AtomicType>, Self::Payload))
        requires
            r.id() == w.id(),
        ensures
            ret.0.is_init(),
            ret.0.ptr() == r.ptr(),
            ret.0.value().into_spec() == w@,
            w@.wf_payload(ret.1),
        opens_invariants
            [r.namespace()]
    ;

    /// Reads, optionally holding an `Observed` for a value seen earlier.
    ///
    /// This thread: gets a value reachable from the one it had, or, with `None`, no claim about
    /// the past at all -- which is where a thread starts.
    /// Other threads: unconstrained. The writer may store again the instant this returns.
    ///
    /// PROPERTY 1 -- reads move forward.
    ///
    /// No payload comes back; see [`RWWithPublishPayloadContract::read_published`].
    fn read(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(past): Tracked<Option<&Observed<Self>>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>))
        requires
            r.ptr() == ptr,
            past is Some ==> r.has_observed(*past->Some_0),
        ensures
            ret.0 == ret.1@@,
            // So the new token can feed the next read.
            r.has_observed(ret.1@),
            // PROPERTY 1. The relation is on pairs, so this says both that the value moved
            // forward and that the payload beside it did -- a reader that knew only about the
            // value would learn nothing that outlives the block it read in, because a writer may
            // swap the payload for any other well-formed one.
            past is Some ==> Self::reachable(past->Some_0.snapshot(), ret.1@.snapshot()),
        opens_invariants any
    ;

    /// Reads with the `WritePerm` in hand, and gets *the* stored value.
    ///
    /// This thread: holds the only `WritePerm`, so no store can be in flight.
    /// Other threads: cannot be writing at all, which is why the value is exact, not reachable.
    ///
    /// PROPERTY 2 -- the relaxation in [`Self::read`] is the price of concurrency, and is
    /// refunded here, where there is none. No `past` is needed: the exact value is strictly more.
    fn read_exact(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&WritePerm<Self>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>))
        requires
            r.ptr() == ptr,
            r.id() == w.id(),
        ensures
            ret.0 == ret.1@@,
            r.has_observed(ret.1@),
            // PROPERTY 2.
            ret.0 == w@,
        opens_invariants any
    ;

    /// Stores `value`, leaving the payload where it is.
    ///
    /// This thread: gets an `Observed` naming what it just stored, so it can read its own write
    /// without going back to the pointer.
    /// Other threads: keep property 1, because `write_value_requires` confines this store to a
    /// pair their `reachable` already admits. That obligation buys every read guarantee.
    fn write(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
    ) -> (ret: Tracked<Observed<Self>>)
        requires
            r.ptr() == ptr,
            r.id() == w.id(),
            old(w).write_value_requires(value),
        ensures
            r.has_observed(ret@),
            ret@@ == value,
            value == final(w)@,
        opens_invariants any
    ;

    /// Stores `value` and swaps in a fresh payload, still unpublished.
    ///
    /// This thread: as [`Self::write`]. No ticket comes back -- an unpublished payload is
    /// reachable only inside the invariant.
    /// Other threads: hold no ticket that this could invalidate. Both `has_published_payload`
    /// preconditions say the slot is empty on either side of the store, so there is none to
    /// invalidate.
    fn write_with_payload(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: Tracked<Observed<Self>>)
        requires
            r.ptr() == ptr,
            r.id() == w.id(),
            old(w).write_value_payload_requires(value, payload),
            !old(w)@.has_published_payload(),
            !value.has_published_payload(),
        ensures
            r.has_observed(ret@),
            ret@@ == value,
            value == final(w)@,
        opens_invariants any
    ;

    /// Replaces the value and unpublished payload without preserving the old observation history.
    ///
    /// Unlike [`Self::write_with_payload`], this operation does not require the replacement to be
    /// reachable from the old value. It therefore consumes `RWShared`, destroys the old invariant,
    /// and returns a rebuilt reader with a fresh observation history. Old observations remain
    /// valid ghost values, but do not satisfy `has_observed` for the rebuilt reader.
    fn write_unrestricted(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (Tracked<RWShared<Self, Self::Payload>>, Tracked<Observed<Self>>))
        requires
            r.ptr() == ptr,
            r.id() == old(w).id(),
            value.wf_payload(payload),
            !value.has_published_payload(),
        ensures
            ret.0@.ptr() == ptr,
            ret.0@.namespace() == r.namespace(),
            ret.0@.id() == final(w).id(),
            ret.0@.has_observed(ret.1@),
            ret.1@@ == value,
            value == final(w)@,
        opens_invariants any
    ;
}

/// The extra guarantees `mrsw_tokens_v2` offers a client that has also implemented
/// [`PublishPayload`] -- property 3, in its two halves.
///
/// This is the whole of the published-payload API's contract. A model that never publishes never
/// implements [`PublishPayload`], never sees these methods, and never names [`PayloadTicket`].
pub trait RWWithPublishPayloadContract: RWContract + PublishPayload {
    /// [`RWContract::read`], plus a ticket when the value has published its payload.
    ///
    /// This thread: PROPERTY 3a -- if the value read has published, a ticket always comes back,
    /// good at this reader's slot and version.
    /// Other threads: each gets its own ticket this way; [`Self::payloads_agree`] is what makes
    /// them all name one payload.
    ///
    /// The `Option` is not redundant: even a publishing model has values that have not published
    /// -- an empty entry -- and those yield no ticket.
    fn read_published(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(past): Tracked<Option<&Observed<Self>>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>, Tracked<Option<PayloadTicket<Self::Payload>>>))
        requires
            r.ptr() == ptr,
            past is Some ==> r.has_observed(*past->Some_0),
        ensures
            ret.0 == ret.1@@,
            r.has_observed(ret.1@),
            // PROPERTY 1; see `RWContract::read`.
            past is Some ==> Self::reachable(past->Some_0.snapshot(), ret.1@.snapshot()),
            // PROPERTY 3a -- a value that has published its payload always yields a ticket for it,
            // and the ticket is good at this reader's slot and version, so it can be presented to
            // `RWShared::borrow_published_payload`.
            ret.0.has_published_payload() ==> {
                &&& ret.2@ is Some
                &&& ret.2@->Some_0.id() == r.slot_id()
                &&& ret.2@->Some_0.version() == r.slot_version()
                &&& ret.0.wf_payload(ret.2@->Some_0.payload())
            },
        opens_invariants any
    ;

    /// PROPERTY 3b -- two tickets at one slot and version name the same payload.
    ///
    /// This thread: two of its own tickets agree.
    /// Other threads: agree with it too -- the statement is over tickets, not readers, so it says
    /// nothing about who holds them. That is the whole content of publishing.
    ///
    /// Stated over tickets because that is the honest form: two premises instead of six, and the
    /// reader-level version follows from what [`Self::read_published`] hands back.
    proof fn payloads_agree(
        tracked t1: &PayloadTicket<Self::Payload>,
        tracked t2: &PayloadTicket<Self::Payload>,
    )
        requires
            t1.id() == t2.id(),
            t1.version() == t2.version(),
        ensures
            t1.payload() == t2.payload(),
    ;

    /// Stores `value` and publishes the payload with it, returning the *first* ticket.
    ///
    /// This thread: as [`RWContract::write`], plus a ticket for the payload just published.
    /// Other threads: may now obtain tickets of their own by reading, and by 3b every one of
    /// them names this payload.
    ///
    /// The only way a payload becomes published, and it happens once: the preconditions say the
    /// slot is empty going in and full coming out.
    fn write_with_published_payload(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (Tracked<Observed<Self>>, Tracked<PayloadTicket<Self::Payload>>))
        requires
            r.ptr() == ptr,
            r.id() == w.id(),
            old(w).write_value_payload_requires(value, payload),
            value.has_published_payload(),
            !old(w)@.has_published_payload(),
        ensures
            r.has_observed(ret.0@),
            ret.0@@ == value,
            value == final(w)@,
            // The ticket is good at this reader's slot and version, so `payloads_agree` applies
            // to it and every ticket a later read mints.
            ret.1@.id() == r.slot_id(),
            ret.1@.version() == r.slot_version(),
            value.wf_payload(ret.1@.payload()),
        opens_invariants any
    ;

    /// Unrestricted replacement that publishes the fresh payload and returns its first ticket.
    fn write_published_unrestricted(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (
        Tracked<RWShared<Self, Self::Payload>>,
        Tracked<Observed<Self>>,
        Tracked<PayloadTicket<Self::Payload>>,
    ))
        requires
            r.ptr() == ptr,
            r.id() == old(w).id(),
            value.wf_payload(payload),
            value.has_published_payload(),
        ensures
            ret.0@.ptr() == ptr,
            ret.0@.namespace() == r.namespace(),
            ret.0@.id() == final(w).id(),
            ret.0@.has_observed(ret.1@),
            ret.1@@ == value,
            value == final(w)@,
            ret.2@.id() == ret.0@.slot_id(),
            ret.2@.version() == ret.0@.slot_version(),
            value.wf_payload(ret.2@.payload()),
        opens_invariants any
    ;
}

} // verus!

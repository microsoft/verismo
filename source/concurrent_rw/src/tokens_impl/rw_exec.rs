//! The executable operations: the reads and writes clients actually call.
//!
//! Everything here runs in `exec` mode and touches the pointer. Its counterpart, [`super`], is
//! entirely ghost: the tokens, the traits a client implements, and the proofs relating them.
//!
//! The ticket-returning operations -- [`read_published`] and
//! [`write_with_published_payload`] -- are bounded on [`PublishPayload`]. A model that never
//! publishes a payload sees only the plain [`read`], [`write`] and
//! [`write_with_payload`], and reaches its payload in-block through `ReaderState::borrow_payload`.
//!
//! Both reads take a `Tracked<Option<Observed<T>>>`: `None` from a thread that holds no token
//! yet, `Some(past)` to also get reachability from a value already seen. One function each, not
//! two, because that argument is the only difference.
//!
//! This is a *child* module of [`super`] rather than a sibling, and that is load-bearing. These
//! operations open the reader's invariant and reach `ReaderState`'s permission and its private
//! proof functions directly. A child module can see its parent's private items and the bodies of
//! its `closed` spec functions, so the split costs no widening at all: nothing became `pub(crate)`
//! and no spec function had to be opened to make it compile.
use super::*;
use crate::tokens_impl::payload_slot::PayloadTicket;
use vstd::atomic::PAtomicUsize;
#[cfg(verus_only)]
use vstd::invariant::create_open_invariant_credit;
#[cfg(verus_only)]
use vstd::invariant::OpenInvariantCredit;
use vstd::open_atomic_invariant;
#[cfg(verus_only)]
use vstd::open_atomic_invariant_in_proof;
use vstd::prelude::*;

verus! {

/// Reads the location, returning the value and an `Observed` token naming it.
///
/// Pass `Tracked(None)` for a thread that holds no `Observed` yet; it gets one back. Pass
/// `Tracked(Some(past))` to additionally guarantee the value handed back is reachable from one
/// seen there earlier -- no read ever moves backwards past a value you already hold.
///
/// No payload comes back. To reach the payload, either open the reader's invariant and use
/// `ReaderState::borrow_payload`, or -- if the model implements `PublishPayload` -- call
/// [`read_published`], which also hands back a ticket.
pub fn read<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(past): Tracked<Option<&Observed<T>>>,
) -> (ret: (T, Tracked<Observed<T>>))
    requires
        r.ptr() == ptr,
        past is Some ==> r.has_observed(*past->Some_0),
    ensures
        ret.0 == ret.1@@,
        r.has_observed(ret.1@),
        // PROPERTY 1: the pair now is reachable from the pair observed.
        past is Some ==> T::reachable(past->Some_0.snapshot(), ret.1@.snapshot()),
{
    let (value, o): (usize, Tracked<Observed<T>>) = read_value(ptr, Tracked(r), Tracked(past));
    proof {
        T::into_from_obeys();
    }
    (value.into(), o)
}

#[verifier::atomic]
pub fn read_value<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(past): Tracked<Option<&Observed<T>>>,
) -> (ret: (T::AtomicType, Tracked<Observed<T>>))
    requires
        r.ptr() == ptr,
        past is Some ==> r.has_observed(*past->Some_0),
    ensures
        ret.0.into_spec() === ret.1@@,
        r.has_observed(ret.1@),
        // PROPERTY 1: the pair now is reachable from the pair observed.
        past is Some ==> T::reachable(past->Some_0.snapshot(), ret.1@.snapshot()),
    opens_invariants
        [r.namespace()],
{
    let value: T::AtomicType;
    let tracked observed;
    proof {
        T::into_from_obeys();
    }
    open_atomic_invariant!(&r.atom => state => {
        proof {
            if past is Some {
                state.read_with_observed(past.tracked_unwrap());
            }
            observed = state.observe();
            assert(observed@ == state.value());
            assert(observed.payload() == state.payload_value());
        }
        value = PAtomicUsize::from_ptr_load(ptr, Tracked(&state.perm));
    });

    (value, Tracked(observed))
}

/// [`read`], and when the value has published its payload, also a ticket for that payload.
///
/// The ticket can later be turned into a `&Payload` with `Reader::borrow_published_payload`,
/// outside any invariant block. The `Option` is not redundant: even a publishing model has values
/// that have not published -- an empty entry -- and those yield no ticket.
///
/// This cannot delegate to [`read`]: minting needs the `PublishPayload` bound, and it has to
/// happen inside the very block that reads, because the ticket's `wf_payload` guarantee is about
/// the value read *there*. A ticket minted afterwards would be well formed for whatever value is
/// stored by then, which is not what a caller needs.
pub fn read_published<T: PublishPayload<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(past): Tracked<Option<&Observed<T>>>,
) -> (ret: (T, Tracked<Observed<T>>, Tracked<Option<PayloadTicket<T::Payload>>>))
    requires
        r.ptr() == ptr,
        past is Some ==> r.has_observed(*past->Some_0),
    ensures
        ret.0 == ret.1@@,
        r.has_observed(ret.1@),
        // PROPERTY 1: the pair now is reachable from the pair observed.
        past is Some ==> T::reachable(past->Some_0.snapshot(), ret.1@.snapshot()),
        ret.0.has_published_payload() ==> {
            &&& ret.2@ is Some
            &&& ret.2@->Some_0.id() == r.slot_id()
            &&& ret.2@->Some_0.version() == r.slot_version()
            &&& ret.0.wf_payload(ret.2@->Some_0.payload())
        },
{
    let value: T::AtomicType;
    let tracked observed;
    let tracked ticket;
    proof {
        T::into_from_obeys();
    }
    open_atomic_invariant!(&r.atom => state => {
        proof {
            if past is Some {
                state.read_with_observed(past.tracked_unwrap());
            }
            observed = state.observe();
            assert(observed@ == state.value());
            assert(observed.payload() == state.payload_value());
            ticket = if state.value().has_published_payload() {
                Some(state.mint_ticket())
            } else {
                None
            };
        }
        value = PAtomicUsize::from_ptr_load(ptr, Tracked(&state.perm));
    });

    (value.into(), Tracked(observed), Tracked(ticket))
}

/// Reads while holding the `Writer`, and returns the value that is stored, exactly.
///
/// This is the one read that escapes the relaxed guarantee. Every other read may only promise a
/// value reachable from one you observed earlier, because a writer could store at any moment.
/// Holding the `Writer` rules that out -- there is no second one -- so `ret.0 == w@` is available
/// here and nowhere else.
pub fn read_exact<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(w): Tracked<&Writer<T>>,
) -> (ret: (T, Tracked<Observed<T>>))
    requires
        r.ptr() == ptr,
        r.id() == w.id(),
    ensures
        r.has_observed(ret.1@),
        ret.1@@ == ret.0,
        ret.0 == w@,
{
    let value: T::AtomicType;
    let tracked observed;
    proof {
        T::into_from_obeys();
    }
    open_atomic_invariant!(&r.atom => state => {
            proof {
                state.read_with_writer(w);
                observed = state.observe();
            }
            value = PAtomicUsize::from_ptr_load(ptr, Tracked(&state.perm));
        });

    (value.into(), Tracked(observed))
}

/// Stores a value together with a fresh payload that is *not* published to readers.
///
/// The `!value.has_published_payload()` precondition is what keeps it unpublished, so no reader
/// can reach it and nothing is promised about agreement. To publish the payload instead, use
/// [`write_with_published_payload`], which returns a `PayloadTicket`.
pub fn write_with_payload<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(w): Tracked<&mut Writer<T>>,
    Tracked(payload): Tracked<T::Payload>,
) -> (ret: Tracked<Observed<T>>)
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
{
    let tracked observed;
    let value_atomic: usize = value.into();
    proof {
        value.into_from_atomic_agree();
        assert(value === value_atomic.into_spec());
    }
    open_atomic_invariant!(&r.atom => state => {
            PAtomicUsize::from_ptr_store(ptr, value_atomic, Tracked(&mut state.perm));
            proof {
                observed = state.update_value_with_payload(w, value, payload);
            }
        });

    Tracked(observed)
}

// Writes a value that publishes its payload for readers to reach, returning the first ticket for
// it. From here on the payload cannot be replaced -- only reclaimed, by surrendering the reader.
pub fn write_with_published_payload<
    T: PublishPayload<AtomicType = usize> + From<usize> + Into<usize>,
>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(w): Tracked<&mut Writer<T>>,
    Tracked(payload): Tracked<T::Payload>,
) -> (ret: (Tracked<Observed<T>>, Tracked<PayloadTicket<T::Payload>>))
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
        ret.1@.id() == r.slot_id(),
        ret.1@.version() == r.slot_version(),
        value.wf_payload(ret.1@.payload()),
{
    let tracked observed;
    let tracked ticket;
    let value_atomic: usize = value.into();
    proof {
        value.into_from_atomic_agree();
        assert(value === value_atomic.into_spec());
    }
    open_atomic_invariant!(&r.atom => state => {
        PAtomicUsize::from_ptr_store(ptr, value_atomic, Tracked(&mut state.perm));
        proof {
            let tracked pair = state.update_value_publishing_payload(w, value, payload);
            observed = pair.0;
            ticket = pair.1;
        }
    });

    (Tracked(observed), Tracked(ticket))
}

/// Stores a value, leaving the payload exactly where it is.
///
/// `write_value_requires` therefore holds the caller to a value that has published a payload if
/// and only if the current one has: a plain store cannot publish. Use [`write_with_payload`] to
/// install a fresh unpublished payload, or [`write_with_published_payload`] to publish one.
pub fn write<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<&Reader<T, T::Payload>>,
    Tracked(w): Tracked<&mut Writer<T>>,
) -> (ret: Tracked<Observed<T>>)
    requires
        r.ptr() == ptr,
        r.id() == w.id(),
        old(w).write_value_requires(value),
    ensures
        r.has_observed(ret@),
        ret@@ == value,
        value == final(w)@,
{
    let tracked observed;
    let value_atomic: usize = value.into();
    proof {
        value.into_from_atomic_agree();
        assert(value === value_atomic.into_spec());
    }
    open_atomic_invariant!(&r.atom => state => {
            PAtomicUsize::from_ptr_store(ptr, value_atomic, Tracked(&mut state.perm));
            proof {
                observed = state.update_value(w, value);
            }
        });

    Tracked(observed)
}

} // verus!

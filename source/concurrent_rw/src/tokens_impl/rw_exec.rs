//! The executable operations: the reads and writes clients actually call.
//!
//! Everything here runs in `exec` mode and touches the pointer. Its counterpart, [`super`], is
//! entirely ghost: the tokens, the traits a client implements, and the proofs relating them.
//!
//! The ticket-returning operations -- [`read_published`] and
//! [`write_with_published_payload`] -- are bounded on [`PublishPayload`]. A model that never
//! publishes a payload sees only the plain [`read`], [`write`] and
//! [`write_with_payload`], and reaches its payload in-block through `RWState::borrow_payload`.
//!
//! Both reads take a `Tracked<Option<Observed<T>>>`: `None` from a thread that holds no token
//! yet, `Some(past)` to also get reachability from a value already seen. One function each, not
//! two, because that argument is the only difference.
//!
//! This is a *child* module of [`super`] rather than a sibling, and that is load-bearing. These
//! operations open the reader's invariant and reach `RWState`'s permission and its private
//! proof functions directly. A child module can see its parent's private items and the bodies of
//! its `closed` spec functions, so the split costs no widening at all: nothing became `pub(crate)`
//! and no spec function had to be opened to make it compile.
use super::*;
use vstd::open_atomic_invariant;
use vstd::prelude::*;

use crate::tokens_impl::payload_slot::PayloadTicket;
use vstd::atomic::PAtomicUsize;
#[cfg(verus_only)]
use vstd::invariant::{create_open_invariant_credit, OpenInvariantCredit};
#[cfg(verus_only)]
use vstd::modes::tracked_swap;
#[cfg(verus_only)]
use vstd::open_atomic_invariant_in_proof;

verus! {

/// Reads the location, returning the value and an `Observed` token naming it.
///
/// Pass `Tracked(None)` for a thread that holds no `Observed` yet; it gets one back. Pass
/// `Tracked(Some(past))` to additionally guarantee the value handed back is reachable from one
/// seen there earlier -- no read ever moves backwards past a value you already hold.
///
/// No payload comes back. To reach the payload, either open the reader's invariant and use
/// `RWState::borrow_payload`, or -- if the model implements `PublishPayload` -- call
/// [`read_published`], which also hands back a ticket.
pub fn read<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
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
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
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
/// The ticket can later be turned into a `&Payload` with `RWShared::borrow_published_payload`,
/// outside any invariant block. The `Option` is not redundant: even a publishing model has values
/// that have not published -- an empty entry -- and those yield no ticket.
///
/// This cannot delegate to [`read`]: minting needs the `PublishPayload` bound, and it has to
/// happen inside the very block that reads, because the ticket's `wf_payload` guarantee is about
/// the value read *there*. A ticket minted afterwards would be well formed for whatever value is
/// stored by then, which is not what a caller needs.
pub fn read_published<T: PublishPayload<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
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

/// Reads while holding the `WritePerm`, and returns the value that is stored, exactly.
///
/// This is the one read that escapes the relaxed guarantee. Every other read may only promise a
/// value reachable from one you observed earlier, because a writer could store at any moment.
/// Holding the `WritePerm` rules that out -- there is no second one -- so `ret.0 == w@` is available
/// here and nowhere else.
pub fn read_exact<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&WritePerm<T>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
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
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
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
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
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
    Tracked(r): Tracked<&RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
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
    let tracked atom = r.borrow_atom();
    open_atomic_invariant!(atom => state => {
            PAtomicUsize::from_ptr_store(ptr, value_atomic, Tracked(&mut state.perm));
            proof {
                observed = state.update_value(w, value);
            }
        });

    Tracked(observed)
}

fn write_unrestricted_inner<
    T: RWModel<AtomicType = usize> + From<usize> + Into<usize>,
>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
    Tracked(payload): Tracked<T::Payload>,
    _publish: bool,
) -> (ret: (
    Tracked<RWShared<T, T::Payload>>,
    Tracked<Observed<T>>,
    Tracked<Option<PayloadTicket<T::Payload>>>,
)) where usize: From<T>
    requires
        r.ptr() == ptr,
        r.id() == old(w).id(),
        value.wf_payload(payload),
        value.has_published_payload() == _publish,
    ensures
        ret.0@.ptr() == r.ptr(),
        ret.0@.namespace() == r.namespace(),
        ret.0@.id() == final(w).id(),
        final(w)@ == value,
        ret.0@.has_observed(ret.1@),
        ret.1@@ == value,
        _publish ==> {
            &&& ret.2@ is Some
            &&& ret.2@->Some_0.id() == ret.0@.slot_id()
            &&& ret.2@->Some_0.version() == ret.0@.slot_version()
            &&& value.wf_payload(ret.2@->Some_0.payload())
        },
        !_publish ==> ret.2@ is None,
    opens_invariants any
{
    let ghost namespace = r.namespace();
    let tracked mut dummy_frac = FracGhost::new(arbitrary());
    let tracked mut old_writer_perm = dummy_frac.split();
    proof {
        use_type_invariant(&r);
        use_type_invariant(&*w);
        tracked_swap(&mut w.perm, &mut old_writer_perm);
    }
    let tracked RWShared { inner: Tracked(old_inner), unique_ns } = r;
    let tracked RWSharedInner { atom, payload_handle } = old_inner;
    let tracked state = atom.into_inner();
    let tracked mut points_to;
    proof {
        let tracked RWState {
            perm,
            payload: old_payload_holder,
            value_frac: mut old_value_frac,
            obs: _,
        } = state;
        old_value_frac.combine(old_writer_perm);
        let tracked _old_payload = old_payload_holder.into_payload(payload_handle);
        points_to = perm;
    }
    let value_atomic: usize = value.into();
    proof {
        value.into_from_atomic_agree();
        assert(value === value_atomic.into_spec());
    }
    PAtomicUsize::from_ptr_store(ptr, value_atomic, Tracked(&mut points_to));
    let tracked reader;
    let tracked observed;
    let tracked ticket;
    proof {
        let ghost snapshot = Snapshot::<T, T::Payload>::new(value, payload);
        let tracked mut value_frac = FracGhost::new(snapshot);
        let tracked new_writer = WritePerm { perm: value_frac.split() };
        let tracked (obs, first) = obs_history::ObsHistory::new(snapshot);
        let tracked (mut payload_holder, payload_handle) = PayloadHolder::new(payload);
        let tracked new_ticket = if _publish {
            Some(payload_holder.publish())
        } else {
            None
        };
        let tracked state = RWState {
            perm: points_to,
            payload: payload_holder,
            value_frac,
            obs,
        };
        T::into_from_obeys();
        assert(value == state.value());
        T::reachable_self(snapshot);
        assert forall|x: Snapshot<T, T::Payload>| state.obs.seen().contains(x) implies
            #[trigger]T::reachable(x, snapshot) by {
            assert(x == snapshot);
        }
        assert(state.inv());
        let constant = state.constant();
        let tracked atom = AtomicInvariant::new(constant, state, namespace);
        let tracked new_inner = RWSharedInner { atom, payload_handle };
        let tracked new_observed = Observed { inner: first };
        reader = RWShared { inner: Tracked(new_inner), unique_ns };
        let tracked WritePerm { perm: mut new_writer_perm } = new_writer;
        tracked_swap(&mut w.perm, &mut new_writer_perm);
        observed = new_observed;
        ticket = new_ticket;
    }
    (Tracked(reader), Tracked(observed), Tracked(ticket))
}

pub fn write_unrestricted<T: RWModel<AtomicType = usize> + From<usize> + Into<usize>>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
    Tracked(payload): Tracked<T::Payload>,
) -> (ret: (Tracked<RWShared<T, T::Payload>>, Tracked<Observed<T>>)) where usize: From<T>
    requires
        r.ptr() == ptr,
        r.id() == old(w).id(),
        value.wf_payload(payload),
        !value.has_published_payload(),
    ensures
        ret.0@.ptr() == r.ptr(),
        ret.0@.namespace() == r.namespace(),
        ret.0@.id() == final(w).id(),
        final(w)@ == value,
        ret.0@.has_observed(ret.1@),
        ret.1@@ == value,
{
    let (Tracked(reader), Tracked(observed), Tracked(ticket)) = write_unrestricted_inner(
        ptr,
        value,
        Tracked(r),
        Tracked(w),
        Tracked(payload),
        false,
    );
    (Tracked(reader), Tracked(observed))
}

pub fn write_published_unrestricted<
    T: PublishPayload<AtomicType = usize> + From<usize> + Into<usize>,
>(
    ptr: *mut usize,
    value: T,
    Tracked(r): Tracked<RWShared<T, T::Payload>>,
    Tracked(w): Tracked<&mut WritePerm<T>>,
    Tracked(payload): Tracked<T::Payload>,
) -> (ret: (
    Tracked<RWShared<T, T::Payload>>,
    Tracked<Observed<T>>,
    Tracked<PayloadTicket<T::Payload>>,
)) where usize: From<T>
    requires
        r.ptr() == ptr,
        r.id() == old(w).id(),
        value.wf_payload(payload),
        value.has_published_payload(),
    ensures
        ret.0@.ptr() == r.ptr(),
        ret.0@.namespace() == r.namespace(),
        ret.0@.id() == final(w).id(),
        final(w)@ == value,
        ret.0@.has_observed(ret.1@),
        ret.1@@ == value,
        ret.2@.id() == ret.0@.slot_id(),
        ret.2@.version() == ret.0@.slot_version(),
        value.wf_payload(ret.2@.payload()),
{
    let (Tracked(reader), Tracked(observed), Tracked(ticket)) = write_unrestricted_inner(
        ptr,
        value,
        Tracked(r),
        Tracked(w),
        Tracked(payload),
        true,
    );
    (Tracked(reader), Tracked(observed), Tracked(ticket.tracked_unwrap()))
}

} // verus!

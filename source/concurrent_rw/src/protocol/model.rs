//! **What a client must supply.** The traits a model implements, with no bodies.
//!
//! Four declarations, and nothing else: what the shared word looks like as a plain integer
//! ([`HasAtomicType`]), what tracked data rides alongside it ([`WithPayload`]), which values a
//! reader may legally see next ([`RWModel`]), and -- only if the model publishes --
//! [`PublishPayload`]. Together they are the whole of a client's obligation.
//!
//! Each has a counterpart in [`crate::protocol::contract`]: satisfy [`RWModel`] and you get
//! `RWContract`; add [`PublishPayload`] and you also get `RWWithPublishPayloadContract`.
//!
//! Neither file mentions a token, an invariant, or a pointer, so the two can be read together as
//! the entire interface without any of the machinery under it.
//!
//! The companion `concurrent_rw_tests` package discharges these traits two different ways -- one
//! publishing its payload, one not -- and stands as evidence that the obligations are
//! dischargeable at all.
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::convert::{FromSpec, FromSpecImpl, IntoSpec};

verus! {

/// A value and its payload, as seen at one moment. Build with [`Snapshot::new`].
///
/// What a reader observes, and what [`RWModel::reachable`] relates. It has to be the pair: a
/// claim about the value alone would say nothing about the payload beside it, since a writer may
/// swap the payload for any other well-formed one.
///
/// The relation must hold for the payload that was *actually* there. Quantifying instead over
/// every payload well formed for the old value would demand that the new payload relate to all of
/// them at once, which no write could satisfy.
#[verifier::accept_recursive_types(T)]
#[verifier::accept_recursive_types(P)]
pub tracked struct Snapshot<T, P> {
    /// `Option` only to give the type a base case. A snapshot sits inside `RWShared`, so it is
    /// recursive -- a payload holds readers, and a reader's state holds a set of snapshots -- and
    /// Verus wants one way to build one that does not recurse. `new` is the only constructor
    /// anyone uses, and `value` and `payload` are meaningless without it.
    pub ghost pair: Option<(T, P)>,
}

impl<T, P> Snapshot<T, P> {
    pub open spec fn new(value: T, payload: P) -> Self {
        Snapshot { pair: Some((value, payload)) }
    }

    pub open spec fn value(self) -> T {
        self.pair->Some_0.0
    }

    pub open spec fn payload(self) -> P {
        self.pair->Some_0.1
    }
}

pub trait WithPayload {
    type Payload;

    spec fn wf_payload(self, payload: Self::Payload) -> bool;
}

pub trait IsValidAtomicType: Sized {
    type AtomicType: From<Self> + Into<Self> + Copy + PartialEq;
}

pub trait RWModel: WithPayload + IsValidAtomicType + Sized {
    /// **The one relation a client supplies:** a preorder on pairs, saying where a value and its
    /// payload may go together, and so what an observer may later see.
    ///
    /// On pairs rather than on values because a claim about the value alone says nothing about
    /// the payload beside it -- a writer may swap the payload for any other well-formed one, so a
    /// reader holding only a value learns nothing that outlives the block it read in. A model
    /// with nothing to say about payloads simply ignores the second component.
    ///
    /// This would read more naturally as `Snapshot<Self, Self::Payload>: Reachable`, but Rust
    /// does not elaborate a trait's `where` clauses to its users, so every generic function over
    /// an `RWModel` would have to repeat the bound. Same relation, stated where it costs nothing.
    spec fn reachable(
        pair: Snapshot<Self, Self::Payload>,
        other: Snapshot<Self, Self::Payload>,
    ) -> bool;

    proof fn reachable_self(pair: Snapshot<Self, Self::Payload>)
        ensures
            Self::reachable(pair, pair),
    ;

    proof fn reachable_transitive(
        a: Snapshot<Self, Self::Payload>,
        b: Snapshot<Self, Self::Payload>,
        c: Snapshot<Self, Self::Payload>,
    )
        requires
            Self::reachable(a, b),
            Self::reachable(b, c),
        ensures
            Self::reachable(a, c),
    ;

    // Whether a value in this state has published its payload for readers to reach.
    //
    // Defaults to `false`: most models never publish, and for them this is the right answer and
    // there is nothing to write. It stays in `RWModel` rather than moving to `PublishPayload`
    // because `RWState`'s invariant ties it to whether the slot really has published, and
    // that equation has to hold for every model, publishing or not.
    open spec fn has_published_payload(self) -> bool {
        false
    }

    proof fn into_from_obeys() where Self: From<Self::AtomicType> + Into<Self::AtomicType>
        ensures
            Self::obeys_from_spec(),
            Self::obeys_into_spec(),
    ;

    proof fn into_from_atomic_agree(self) where
        Self: From<Self::AtomicType> + Into<Self::AtomicType>,

        ensures
            Self::obeys_from_spec(),
            Self::obeys_into_spec(),
            self === Self::AtomicType::from_spec(self).into_spec(),
    ;
}

/// Opt-in: this model publishes payloads, so a reader may carry a payload reference *out* of the
/// invariant block it came from.
///
/// `RWModel` on its own already supports payloads, but only inside `open_atomic_invariant!` --
/// see [`RWState::borrow_payload`]. That is enough to read a payload and copy plain data out
/// of it, and a model that never needs more should stop there: it then never names
/// [`PayloadTicket`] at all, and its reads return just a value and an `Observed`.
///
/// Implementing this trait additionally enables the published route: `read_published` and
/// `write_with_published_payload` on
/// [`RWWithPublishPayloadContract`](crate::protocol::contract::RWWithPublishPayloadContract),
/// plus [`RWShared::borrow_published_payload`].
///
/// A model that opts in must also override `RWModel::has_published_payload`, which defaults to
/// `false`. That spec function stays in `RWModel` because the reader's invariant ties it to
/// whether the slot really has published, and that equation has to hold for every model. Only the
/// *proof* obligation lives here.
///
/// ```ignore
/// impl RWModel for PTEntry {
///     open spec fn has_published_payload(self) -> bool { self.present() }
///     // ...
/// }
///
/// impl PublishPayload for PTEntry {
///     proof fn payload_stays_published(
///         pair: Snapshot<Self, Self::Payload>,
///         next: Snapshot<Self, Self::Payload>,
///     ) {}
/// }
/// ```
pub trait PublishPayload: RWModel {
    // Publishing is one-way along read-reachability: a value that has published can only be
    // followed, by reading, by values that have also published. This is what stops a concurrent
    // write from undercutting a ticket a reader already holds.
    //
    // The whole obligation, and the only one this trait adds. It once also demanded that
    // reachable values agree on which payloads are well formed, which was never used: the library
    // re-derives `value.wf_payload(payload)` from the invariant on every read, so no client ever
    // needed to transport it across a write.
    proof fn payload_stays_published(
        pair: Snapshot<Self, Self::Payload>,
        next: Snapshot<Self, Self::Payload>,
    )
        requires
            pair.value().has_published_payload(),
            Self::reachable(pair, next),
        ensures
            next.value().has_published_payload(),
    ;
}

} // verus!

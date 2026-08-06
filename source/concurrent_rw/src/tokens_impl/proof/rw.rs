//! **The tokens themselves.** What a `RWShared`, `WritePerm`, `Observed` and `PayloadTicket` are,
//! and the ghost operations over them. Entirely ghost: the operations that touch the pointer
//! live in [`rw_exec`], a child module so that it can reach the private items here.
//!
//! [`super`] carries the reading -- how the pieces fit together and why each one is shaped the
//! way it is.
// A child, not a sibling, so that it can see the private items and `closed` spec bodies below.
// `rw_exec.rs` remains in the parent directory because it is executable rather than proof code.
#[path = "../rw_exec.rs"]
pub(crate) mod rw_exec;

#[cfg(all(feature = "state_machine", verus_only))]
use crate::tokens_impl::frac_perm_proof::FracGhost;
#[cfg(any(not(feature = "state_machine"), not(verus_only)))]
use vstd::resource::frac::FracGhost;

pub use crate::protocol::model::{
    IsValidAtomicType, PublishPayload, RWModel, Snapshot, WithPayload,
};

// The sibling modules by name: this file was `mod.rs` once, where they needed no import.
use vstd::prelude::*;

use crate::tokens_impl::obs_history;
#[cfg(verus_only)]
use crate::tokens_impl::payload_slot::PayloadTicket;
use crate::tokens_impl::payload_slot::{PayloadHolder, SlotHandle};
#[cfg(verus_only)]
use crate::trusted_t::{axiom_loc_to_int_injective, loc_to_int};
#[cfg(verus_only)]
use vstd::invariant::OpenInvariantCredit;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::raw_ptr::PointsTo;
use vstd::resource::algebra::Resource;
#[cfg(verus_only)]
use vstd::resource::frac::lemma_whole_fraction_has_no_frame;
use vstd::resource::frac::FractionRA;
#[cfg(any(not(feature = "state_machine"), not(verus_only)))]
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::std_specs::convert::{FromSpec, FromSpecImpl, IntoSpec};
#[cfg(verus_only)]
use vstd::{open_atomic_invariant, open_atomic_invariant_in_proof};

verus! {

// ---------------------------------------------------------------------------------------
// The types.
// ---------------------------------------------------------------------------------------
pub ghost struct RWConstant<T: IsValidAtomicType> {
    value_frac_id: Loc,  // frac id of the value fraction
    obs_id: Loc,  // identity of the observation history
    ptr: *const T::AtomicType,  // the root pointer
    slot_id: Loc,  // identity of the payload slot
    slot_version: nat,  // the slot version this shared token is good for
}

/// Evidence that this reader saw this value, with this payload beside it.
pub tracked struct Observed<T: RWModel> {
    tracked inner: obs_history::Observed<Snapshot<T, T::Payload>>,
}

pub tracked struct RWState<T: IsValidAtomicType, Payload> {
    // The memory permission to the value, paired with the `IsExposed` provenance token of the
    // page it lives in. The token lets us rebuild the exec pointer to this entry at read time.
    pub tracked perm: PointsTo<T::AtomicType>,
    pub tracked payload: PayloadHolder<Payload>,
    // Half of the value-and-payload pair; the `WritePerm` holds the other half, which is what makes
    // it the only writer.
    pub tracked value_frac: FracGhost<Snapshot<T, Payload>>,
    // Every pair anyone has observed, and the guarantee that each still reaches the present one.
    pub tracked obs: obs_history::ObsHistory<Snapshot<T, Payload>>,
}

pub tracked struct WritePerm<T: RWModel> {
    perm: FracGhost<Snapshot<T, T::Payload>>,
}

tracked struct RWSharedInner<T: IsValidAtomicType, Payload> {
    tracked atom: AtomicInvariant<RWConstant<T>, RWState<T, Payload>, RWState<T, Payload>>,
    tracked payload_handle: SlotHandle<Payload>,
}

// The shared capability for one location: it owns that location's atomic invariant. There is one
// per pointer; multiple readers borrow it as `&RWShared`. Reads and writes open the same invariant,
// so consistency comes from the invariant rather than from keeping them apart.
pub tracked struct RWShared<T: IsValidAtomicType, Payload> {
    inner: Tracked<RWSharedInner<T, Payload>>,
    // token representing the unique namespace of the atom.
    unique_ns: Tracked<Resource<FractionRA>>,
}

// ---------------------------------------------------------------------------------------
// The operations.
// ---------------------------------------------------------------------------------------
impl<T: IsValidAtomicType> RWConstant<T> {
    /// The id of the whole value fraction, which is what a `WritePerm` is a share of.
    pub closed spec fn value_frac_id(&self) -> Loc {
        self.value_frac_id
    }

    /// Identity of the payload slot this reader is attached to.
    pub closed spec fn slot_id(&self) -> Loc {
        self.slot_id
    }

    /// The slot version this reader is good for.
    pub closed spec fn slot_version(&self) -> nat {
        self.slot_version
    }

    /// Identity of the observation history.
    pub closed spec fn obs_id(&self) -> Loc {
        self.obs_id
    }
}

impl<T: RWModel> RWConstant<T> {
    /// Whether this token came from this shared location's history. One id now, rather than one per
    /// value: the history is a single instance, so the check no longer depends on what was seen.
    pub open spec fn has_observed(&self, observed: Observed<T>) -> bool {
        self.obs_id() == observed.id()
    }
}

impl<T: RWModel> View for Observed<T> {
    type V = T;

    open spec fn view(&self) -> T {
        self.value()
    }
}

impl<T: RWModel> Observed<T> {
    /// Which shared location's history this came from.
    pub closed spec fn id(&self) -> Loc {
        self.inner.id()
    }

    /// The value that was seen.
    pub open spec fn value(&self) -> T {
        self.snapshot().value()
    }

    /// The payload that was beside it. What the model's relation carries forward, and the reason
    /// an observation names a pair rather than a value.
    pub open spec fn payload(&self) -> T::Payload {
        self.snapshot().payload()
    }

    /// The value and payload that were seen, together -- what the model's relation relates.
    pub closed spec fn snapshot(&self) -> Snapshot<T, T::Payload> {
        self.inner.value()
    }

    /// Another copy. Free, where the old fractional token had to be split.
    pub proof fn duplicate(tracked &self) -> (tracked result: Self)
        ensures
            result.id() == self.id(),
            result.value() == self.value(),
            result.payload() == self.payload(),
    {
        Observed { inner: self.inner.duplicate() }
    }
}

impl<T: RWModel> WritePerm<T> {
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        self.perm.frac() == 0.5real
    }

    pub open spec fn view(&self) -> T {
        self.current_snapshot().value()
    }

    /// The payload sitting beside the value right now.
    ///
    /// The writer owns the payload, so it may as well know what it is -- and it has to, because
    /// [`Self::write_value_payload_requires`] relates the payload going in to the one coming out,
    /// and that relation has to name the payload that is actually there. Quantifying over every
    /// payload well formed for the current value instead would be unsatisfiable: no single new
    /// payload can relate to all of them.
    pub open spec fn payload(&self) -> T::Payload {
        self.current_snapshot().payload()
    }

    /// The pair in the slot right now, which is what the model's relation is about. `current`
    /// to keep it apart from `Observed::snapshot`, which names a pair from the past.
    pub closed spec fn current_snapshot(&self) -> Snapshot<T, T::Payload> {
        self.perm@
    }

    pub closed spec fn id(&self) -> Loc {
        self.perm.id()
    }

    pub closed spec fn frac(&self) -> real {
        self.perm.frac()
    }

    pub open spec fn write_value_requires(&self, value: T) -> bool {
        &&& T::reachable(
            self.current_snapshot(),
            Snapshot::new(value, self.payload()),
        )
        // The payload stays put, so only the one that is really there need stay well formed.
        // This used to quantify over every well-formed payload, which asked far more than the
        // write needs now that the writer can name the payload it holds.
        &&& value.wf_payload(
            self.payload(),
        )
        // A plain write leaves the payload where it is, so it cannot publish one.
        &&& value.has_published_payload() == self@.has_published_payload()
    }

    pub open spec fn write_value_payload_requires(&self, value: T, payload: T::Payload) -> bool {
        // The one obligation on a write, and the whole of it: land inside the model's own
        // relation. Replacing the payload is covered because the relation is about pairs.
        &&& T::reachable(self.current_snapshot(), Snapshot::new(value, payload))
        &&& value.wf_payload(payload)
    }
}

impl<T: IsValidAtomicType, Payload> RWState<T, Payload> {
    /// The value this state holds.
    pub closed spec fn value(&self) -> T {
        self.value_frac@.value()
    }

    // The id of the RWShared, the real constant of the shared token. Open, and routed through
    // `constant()`, so that a proof outside this module can tie it to the `RWShared` the invariant
    // came from -- see `RWShared::id`.
    pub open spec fn id(&self) -> Loc {
        self.constant().value_frac_id()
    }

    // Constant in AtomicInvariant
    pub closed spec fn constant(&self) -> RWConstant<T> {
        RWConstant {
            value_frac_id: self.value_frac.id(),
            obs_id: self.obs.id(),
            ptr: self.perm.ptr(),
            slot_id: self.payload.id(),
            slot_version: self.payload.version(),
        }
    }
}

impl<T: RWModel> RWState<T, T::Payload> {
    /// Pins the payload this state holds to a ticket for the same slot.
    ///
    /// `borrow_payload` alone says only "the payload right now", which is all a caller can want
    /// while it is unpublished. Once it is published it is also *fixed*, and this is how a client
    /// cashes that in: two blocks that each borrow the payload get the same one, because both
    /// agree with the ticket. Mints a ticket internally and discards it, which leaves the slot's
    /// version, contents and well-formedness untouched.
    pub proof fn lemma_payload_agrees_with_ticket(
        tracked &mut self,
        tracked r: &RWShared<T, T::Payload>,
        tracked ticket: &PayloadTicket<T::Payload>,
    )
        requires
            old(self).inv(),
            old(self).constant() == r.constant(),
            r.slot_id() == ticket.id(),
            r.slot_version() == ticket.version(),
            old(self).value().has_published_payload(),
        ensures
            final(self).inv(),
            final(self).constant() == old(self).constant(),
            final(self).value() == old(self).value(),
            final(self).payload_value() == ticket.payload(),
    {
        let tracked minted = self.payload.mint_ticket();
        minted.agree(ticket);
    }

    /// The payload this state holds, wherever it currently lives.
    pub closed spec fn payload_value(&self) -> T::Payload {
        self.payload.payload()
    }

    /// What `inv()` says about the memory permission, which is otherwise sealed inside it.
    ///
    /// A client that opens an `RWShared` invariant holds the state but can see nothing about `perm`,
    /// because `inv` is closed and `RWConstant`'s fields are private. This relates the state
    /// back to the `RWShared` it came from: pair it with `RWShared::borrow_atom`, whose `constant()`
    /// equality is what discharges the precondition.
    pub proof fn lemma_inv_perm(tracked &self, tracked r: &RWShared<T, T::Payload>)
        requires
            self.inv(),
            self.constant() == r.constant(),
        ensures
            self.perm.is_init(),
            self.perm.ptr() == r.ptr(),
            self.perm.value().into_spec() == self.value(),
    {
    }

    /// Borrows the payload while it is still unpublished.
    ///
    /// Only reachable inside `open_atomic_invariant!` on the `RWShared` this state came from, and
    /// the borrow dies with the block: an unpublished payload cannot leave. The well-formedness
    /// handed back is against `value()`, the value *now*, not against any value read earlier --
    /// while a payload is unpublished a writer may replace it at any time, so there is nothing to
    /// carry a claim across blocks. Publishing is what removes that freedom.
    pub proof fn borrow_payload<'a>(tracked &'a self, c: RWConstant<T>) -> (tracked out:
        &'a T::Payload)
        requires
            <Self as InvariantPredicate<RWConstant<T>, Self>>::inv(c, *self),
        ensures
            *out == self.payload_value(),
            self.value().wf_payload(*out),
    {
        self.payload.borrow_payload()
    }

    /// Borrows the payload mutably, while it is still unpublished. Lend, do not keep: put the
    /// payload back as you found it and the last clause hands the whole state back unchanged,
    /// so `inv` still holds and the block can close.
    ///
    /// It cannot promise more. `current_snapshot()` is the value *and* the payload, so a payload
    /// that really changed moves it, and two clauses of `inv_frac` go with it -- `value_frac@`
    /// and `obs.seen()`. Restoring those is `RWState::update`'s job: it needs the `WritePerm`'s
    /// half of the fraction and an `obs.insert`, and neither can run after a borrow is handed
    /// back. What this is for is calling `&mut` proof functions that end where they started,
    /// `RWShared::distinct_namespace` above all.
    pub proof fn borrow_payload_mut<'a>(tracked &'a mut self, c: RWConstant<T>) -> (tracked out:
        &'a mut T::Payload)
        requires
            <Self as InvariantPredicate<RWConstant<T>, Self>>::inv(c, *old(self)),
            !old(self).value().has_published_payload(),
        ensures
            *out == old(self).payload_value(),
            old(self).value().wf_payload(*out),
            final(self).payload_value() == *final(out),
            final(self).value() == old(self).value(),
            final(self).constant() == old(self).constant(),
            (*final(out) == *out) <==> *final(self) == *old(self),
    {
        self.payload.borrow_payload_mut()
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.inv_perm(self.value())
        &&& self.inv_frac()
    }

    spec fn inv_perm(&self, value: T) -> bool {
        &&& self.perm.is_init()
        &&& self.perm.value().into_spec() === value
    }

    /// The pair in the slot right now, which is what both the writer's fraction and the
    /// observation history are about.
    pub open spec fn current_snapshot(&self) -> Snapshot<T, T::Payload> {
        self.new_snapshot(self.value())
    }

    /// The pair this state would hold if the value were `value`, with the payload it holds now.
    pub open spec fn new_snapshot(&self, value: T) -> Snapshot<T, T::Payload> {
        Snapshot::new(value, self.payload_value())
    }

    spec fn inv_frac(&self) -> bool {
        &&& self.payload.wf()
        &&& self.value().wf_payload(
            self.payload_value(),
        )
        // Publishing is one-way, and a value that claims to have published really has.
        &&& self.value().has_published_payload() == self.payload.is_published()
        &&& self.value_frac.frac()
            == 0.5real
        // The fraction agrees with the payload actually held.
        &&& self.value_frac@
            == self.current_snapshot()
        // The whole guarantee an RWShared token buys, kept here rather than inside the history:
        // everything ever seen still reaches the pair stored now. `obs_history::ObsHistory` cannot state it --
        // the bound would land on `RWShared`, and payloads hold readers -- but it does supply the
        // one thing that makes it worth stating, which is that the set only grows.
        &&& self.obs.seen().contains(self.current_snapshot())
        &&& forall|x: Snapshot<T, T::Payload>| #[trigger]
            self.obs.seen().contains(x) ==> T::reachable(x, self.current_snapshot())
    }

    proof fn update_value_with_payload(
        tracked &mut self,
        tracked writer: &mut WritePerm<T>,
        value: T,
        tracked payload: T::Payload,
    ) -> (tracked observed: Observed<T>) where T: From<T::AtomicType> + Into<T::AtomicType>
        requires
            old(writer).write_value_payload_requires(value, payload),
            // Replacing the payload is only possible while it is still private -- so neither the
            // value being overwritten nor the one going in may have published. For a model that
            // never publishes both are free; a `PublishPayload` model gets the first from the
            // second through `payload_stays_published`.
            !old(writer)@.has_published_payload(),
            !value.has_published_payload(),
            old(self).inv_frac(),
            old(self).inv_perm(value),
            writer.id() == self.id(),
        ensures
            final(self).inv(),
            old(self).constant() == final(self).constant(),
            final(writer).id() == old(self).id(),
            final(writer)@ == value,
            old(self).constant().has_observed(observed),
            observed@ == value,
    {
        let tracked (observed, ticket) = self.update(writer, value, false, Option::Some(payload));
        observed
    }

    /// The ghost half of a write, shared by the three `update_value*` entry points: swing the
    /// value fraction, put the payload in place, publish it if asked, and record the new pair in
    /// the history.
    ///
    /// `payload` is `Some` when the write replaces the payload and `None` when it leaves it
    /// alone; either way the caller has already shown the new pair lands inside the model's
    /// relation. Publishing happens here rather than in the caller because between storing a
    /// value that claims to have published and actually publishing, `inv_frac` does not hold.
    proof fn update(
        tracked &mut self,
        tracked writer: &mut WritePerm<T>,
        value: T,
        publish: bool,
        tracked payload: Option<T::Payload>,
    ) -> (tracked out: (Observed<T>, Option<PayloadTicket<T::Payload>>)) where
        T: From<T::AtomicType> + Into<T::AtomicType>,

        requires
            match payload {
                Some(p) => {
                    &&& old(writer).write_value_payload_requires(
                        value,
                        p,
                    )
                    // The payload being replaced must still be private.
                    &&& !old(writer)@.has_published_payload()
                    &&& value.has_published_payload() == publish
                },
                None => old(writer).write_value_requires(value) && !publish,
            },
            old(self).inv_frac(),
            old(self).inv_perm(value),
            writer.id() == self.id(),
        ensures
            final(self).inv(),
            final(self).value() == value,
            final(self).payload_value() == match payload {
                Some(p) => p,
                None => old(self).payload_value(),
            },
            old(self).constant() == final(self).constant(),
            final(writer).id() == old(self).id(),
            final(writer)@ == value,
            final(writer).payload() == final(self).payload_value(),
            old(self).constant().has_observed(out.0),
            out.0.value() == value,
            out.0.payload() == final(self).payload_value(),
            out.1 is Some <==> publish,
            publish ==> {
                &&& out.1->Some_0.id() == old(self).constant().slot_id()
                &&& out.1->Some_0.version() == old(self).constant().slot_version()
                &&& value.wf_payload(out.1->Some_0.payload())
            },
    {
        writer.perm.agree(&self.value_frac);
        use_type_invariant(&*writer);
        let ghost old_snapshot = self.current_snapshot();
        if let Option::Some(p) = payload {
            self.payload.replace(p);
        }
        let ghost new_snapshot = self.new_snapshot(value);
        self.value_frac.update_with(&mut writer.perm, new_snapshot);
        let tracked ticket = if publish {
            Option::Some(self.payload.publish())
        } else {
            Option::None
        };
        let tracked observed = self.obs.insert(new_snapshot);
        // Everything seen before reached the pair being replaced, and that pair reaches the new
        // one, so a single use of transitivity carries the whole set forward.
        assert forall|x: Snapshot<T, T::Payload>| #[trigger]
            self.obs.seen().contains(x) implies T::reachable(x, new_snapshot) by {
            if x == new_snapshot {
                T::reachable_self(x);
            } else {
                T::reachable_transitive(x, old_snapshot, new_snapshot);
            }
        }
        (Observed { inner: observed }, ticket)
    }

    proof fn update_value(
        tracked &mut self,
        tracked writer: &mut WritePerm<T>,
        value: T,
    ) -> (tracked observed: Observed<T>) where T: From<T::AtomicType> + Into<T::AtomicType>
        requires
            old(writer).write_value_requires(value),
            old(self).inv_frac(),
            old(self).inv_perm(value),
            writer.id() == self.id(),
        ensures
            final(self).inv(),
            old(self).constant() == final(self).constant(),
            final(writer).id() == old(self).id(),
            final(writer)@ == value,
            old(self).constant().has_observed(observed),
            observed@ == value,
    {
        let tracked (observed, ticket) = self.update(writer, value, false, Option::None);
        observed
    }

    /// Mint an `Observed` token for the value currently in the slot.
    ///
    /// `pub` because [`super::contract_proof`] discharges the contract from outside this module, and
    /// this is one of the two ghost steps a read is made of. It sits at the same layer as
    /// [`Self::read_with_observed`]: both need `&mut RWState`, which is only reachable by
    /// opening the shared location's invariant.
    pub proof fn observe(tracked &mut self) -> (tracked observed: Observed<T>) where
        T: From<T::AtomicType> + Into<T::AtomicType>,

        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).constant() == old(self).constant(),
            final(self).value() == old(self).value(),
            old(self).constant().has_observed(observed),
            final(self).payload_value() == old(self).payload_value(),
            observed.snapshot() == final(self).current_snapshot(),
    {
        Observed { inner: self.obs.observe(self.current_snapshot()) }
    }

    /// What a token bought: the value it names still reaches the value now, and the payload it
    /// names still reaches the payload now.
    ///
    /// Takes `&self`, not `&mut self`: reading the history changes nothing.
    pub proof fn read_with_observed(tracked &self, tracked observed: &Observed<T>)
        requires
            self.inv(),
            self.constant().has_observed(*observed),
        ensures
            T::reachable(observed.snapshot(), self.current_snapshot()),
    {
        self.obs.is_seen(&observed.inner);
    }

    /// `pub` alongside [`Self::observe`]: [`super::contract_proof`] needs it to discharge
    /// `RWContract::read_exact`.
    pub proof fn read_with_writer(tracked &self, tracked writer: &WritePerm<T>)
        requires
            self.inv(),
            self.id() == writer.id(),
        ensures
            self.value() == writer@,
            self.payload_value() == writer.payload(),
    {
        writer.perm.agree(&self.value_frac);
    }
}

// The published-payload half of `RWState`, available only to a model that opted in with
// `PublishPayload`. Everything here mints or consumes a `PayloadTicket`; a model that never
// publishes never sees these, and never names `PayloadTicket`.
impl<T: PublishPayload> RWState<T, T::Payload> {
    // Writes a value that publishes its payload into the slot, and returns the first ticket for
    // it. From here on the payload stays put and readers may borrow it; it comes back out only
    // through `reclaim`, which consumes the reader's handle.
    proof fn update_value_publishing_payload(
        tracked &mut self,
        tracked writer: &mut WritePerm<T>,
        value: T,
        tracked payload: T::Payload,
    ) -> (tracked out: (Observed<T>, PayloadTicket<T::Payload>)) where
        T: From<T::AtomicType> + Into<T::AtomicType>,

        requires
            old(writer).write_value_payload_requires(value, payload),
            value.has_published_payload(),
            // The payload being replaced must still be unpublished, so the value being
            // overwritten cannot already have published one.
            !old(writer)@.has_published_payload(),
            old(self).inv_frac(),
            old(self).inv_perm(value),
            writer.id() == self.id(),
        ensures
            final(self).inv(),
            old(self).constant() == final(self).constant(),
            final(writer).id() == old(self).id(),
            final(writer)@ == value,
            old(self).constant().has_observed(out.0),
            out.0@ == value,
            out.1.id() == old(self).constant().slot_id(),
            out.1.version() == old(self).constant().slot_version(),
            value.wf_payload(out.1.payload()),
    {
        let tracked (observed, ticket) = self.update(writer, value, true, Option::Some(payload));
        let tracked ticket = match ticket {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        };
        (observed, ticket)
    }

    // Hands out another ticket for a payload that is already published.
    /// `pub` for the same reason as [`Self::observe`]: [`super::contract_proof`] needs it, and
    /// it is already gated twice over -- by `PublishPayload` on the impl, and by
    /// `has_published_payload()` in the requires.
    pub proof fn mint_ticket(tracked &mut self) -> (tracked out: PayloadTicket<T::Payload>)
        requires
            old(self).inv(),
            old(self).value().has_published_payload(),
        ensures
            final(self).inv(),
            final(self).constant() == old(self).constant(),
            final(self).value() == old(self).value(),
            out.id() == old(self).constant().slot_id(),
            out.version() == old(self).constant().slot_version(),
            old(self).value().wf_payload(out.payload()),
    {
        self.payload.mint_ticket()
    }
}

impl<T: RWModel> InvariantPredicate<RWConstant<T>, RWState<T, T::Payload>> for RWState<
    T,
    T::Payload,
> {
    // Open, so that a client opening the invariant can actually use what it is handed.
    open spec fn inv(constant: RWConstant<T>, v: RWState<T, T::Payload>) -> bool {
        v.inv() && v.constant() == constant
    }
}

impl<T: IsValidAtomicType, Payload> RWShared<T, Payload> {
    /// Two readers have different namespaces.
    ///
    /// Needs `&mut` on one side, and that is not a detail of the proof -- it is the claim. Two
    /// shared references may be the *same* reference, and then the namespaces are equal. So the
    /// exclusivity has to come from somewhere, and `&mut` is where.
    pub proof fn distinct_namespace(tracked &mut self, tracked other: &Self)
        ensures
            final(self).namespace() != other.namespace(),
            *final(self) == *old(self),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.unique_ns@.loc() == other.unique_ns@.loc() {
            // Two whole fractions at one location: their composition would have to be valid.
            self.unique_ns.borrow_mut().validate_2(other.unique_ns.borrow());
            lemma_whole_fraction_has_no_frame(FractionRA::Frac(1.0real));
            assert(false);
        }
        axiom_loc_to_int_injective(self.unique_ns@.loc(), other.unique_ns@.loc());
    }

    pub closed spec fn constant(&self) -> RWConstant<T> {
        self.inner@.atom.constant()
    }

    // The id of the whole value fraction.
    pub open spec fn id(&self) -> Loc {
        self.constant().value_frac_id()
    }

    pub closed spec fn namespace(&self) -> int {
        self.inner@.atom.namespace()
    }

    pub closed spec fn ptr(&self) -> *const T::AtomicType {
        self.constant().ptr
    }

    // Identity of this shared location's payload slot. Open, and routed through `constant()`, so a
    // proof outside this module can connect it to the `RWConstant` it gets from opening the
    // invariant.
    pub open spec fn slot_id(&self) -> Loc {
        self.constant().slot_id()
    }

    // Identity of this shared location's observation history. Two shared tokens with the same one
    // accept each
    // other's `Observed` tokens -- see `has_observed` -- which is what a client needs to say when
    // it wants an observation of a child to survive from one invariant block to the next.
    pub open spec fn obs_id(&self) -> Loc {
        self.constant().obs_id()
    }

    // The slot version this shared token is good for. A ticket from an earlier version no longer
    // grants access, which is how reclaiming a payload cuts every reader off at once.
    pub open spec fn slot_version(&self) -> nat {
        self.constant().slot_version()
    }

    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        // A whole fraction, at the location the namespace names. Both halves matter: whole, so
        // it cannot be shared with another reader, and named, so the exclusivity reaches the
        // namespace.
        &&& self.unique_ns@.value() == FractionRA::Frac(1.0real)
        &&& self.inner@.payload_handle.id() == self.slot_id()
        &&& self.inner@.payload_handle.version() == self.slot_version()
        &&& self.namespace() == loc_to_int(self.unique_ns@.loc())
    }

    // Hands out the shared location's atomic invariant so a client can open it. This is the only way to
    // reach an *unpublished* payload; see `RWState::borrow_payload`.
    pub proof fn borrow_atom(tracked &self) -> (tracked out: &AtomicInvariant<
        RWConstant<T>,
        RWState<T, Payload>,
        RWState<T, Payload>,
    >)
        ensures
            out.constant() == self.constant(),
            out.namespace() == self.namespace(),
    {
        use_type_invariant(self);
        &self.inner.borrow().atom
    }
}

impl<T: RWModel, Payload> RWShared<T, Payload> {
    pub open spec fn has_observed(&self, observed: Observed<T>) -> bool {
        self.constant().has_observed(observed)
    }
}

impl<T: RWModel> RWShared<T, T::Payload> {
    /// Two readers guard disjoint memory.
    ///
    /// The pointers live inside the two invariants, so the only way to compare them is to hold
    /// both open at once -- which needs their namespaces distinct, which is what
    /// `distinct_namespace` supplies. Hence the same `&mut`: without it the claim is false, since
    /// a reader does not guard memory disjoint from itself.
    ///
    /// The credits are the price of opening an invariant from proof code, where
    /// `create_open_invariant_credit` (an exec function) cannot be called.
    pub proof fn disjoint_ptr(
        tracked &mut self,
        tracked other: &Self,
        tracked credit_self: OpenInvariantCredit,
        tracked credit_other: OpenInvariantCredit,
    )
        requires
            size_of::<T::AtomicType>() != 0,
        ensures
            final(self).ptr() as int + size_of::<T::AtomicType>() <= other.ptr() as int
                || other.ptr() as int + size_of::<T::AtomicType>() <= final(self).ptr() as int,
            *final(self) == *old(self),
        opens_invariants [self.namespace(), other.namespace()]
    {
        self.distinct_namespace(other);
        let tracked self_atom = self.borrow_atom();
        let tracked other_atom = other.borrow_atom();
        open_atomic_invariant_in_proof!(credit_self => self_atom => s1 => {
            open_atomic_invariant_in_proof!(credit_other => other_atom => s2 => {
                s1.perm.is_disjoint(&s2.perm);
            });
        });
    }
}

// The published-payload half of `RWShared`, available only to a model that opted in with
// `PublishPayload`.
impl<T: PublishPayload> RWShared<T, T::Payload> {
    // Looks at a published payload through a ticket for it, handing back a reference that outlives
    // the atomic-invariant block the ticket came from. This is the one thing an `AtomicInvariant`
    // cannot do on its own.
    pub proof fn borrow_published_payload<'a, 's>(
        tracked &'a self,
        tracked ticket: &'s PayloadTicket<T::Payload>,
    ) -> (tracked out: &'s T::Payload) where 'a: 's
        requires
            self.slot_id() == ticket.id(),
            self.slot_version() == ticket.version(),
        ensures
            *out == ticket.payload(),
    {
        use_type_invariant(self);
        self.inner.borrow().payload_handle.borrow(ticket)
    }
}

impl<T: RWModel> RWShared<T, T::Payload> where
    T: From<T::AtomicType> + Into<T::AtomicType>,
    T::AtomicType: From<T>,
 {
    pub proof fn new(
        value: T,
        tracked points_to: PointsTo<T::AtomicType>,
        tracked payload: T::Payload,
    ) -> (tracked ret: (RWShared<T, T::Payload>, WritePerm<T>, Observed<T>))
        requires
            points_to.is_init(),
            points_to.value().into_spec() === value,
            value.wf_payload(payload),
            !value.has_published_payload(),
        ensures
            ret.0.ptr() == points_to.ptr(),
            ret.0.id() == ret.1.id(),
            // The first `Observed`, for the value stored at the hand-over. Whoever gives up
            // exclusive access knows what was in it, so this is where the first one is issued.
            ret.2@ == value,
            ret.0.has_observed(ret.2),
    {
        let ghost snapshot = Snapshot::<T, T::Payload>::new(value, payload);
        let tracked mut value_frac = FracGhost::new(snapshot);
        let tracked writer = WritePerm { perm: value_frac.split() };
        let tracked (obs, first) = obs_history::ObsHistory::new(snapshot);
        let tracked (payload, handle) = PayloadHolder::new(payload);
        let tracked mut reader_state = RWState { perm: points_to, payload, value_frac, obs };
        T::into_from_obeys();
        assert(value == reader_state.value());
        let constant = reader_state.constant();
        T::reachable_self(snapshot);
        assert(reader_state.inv());
        let tracked observed = Observed { inner: first };
        // The namespace *is* the fraction's location. Minting the fraction first and naming the
        // invariant after it is what makes `distinct_namespace` provable: the fraction is whole,
        // so no other reader can ever hold one at this location.
        let tracked ns = Resource::<FractionRA>::alloc(FractionRA::Frac(1.0real));
        let tracked invariant = AtomicInvariant::new(constant, reader_state, loc_to_int(ns.loc()));
        let tracked inner = RWSharedInner { atom: invariant, payload_handle: handle };
        let tracked reader = RWShared {
            inner: Tracked(inner),
            unique_ns: Tracked(ns),
        };
        let tracked out = (reader, writer, observed);
        out
    }

    /// Destroys the shared protocol and recovers the exclusive permission and payload.
    pub proof fn teardown(
        tracked self,
        tracked writer: WritePerm<T>,
    ) -> (tracked out: (PointsTo<T::AtomicType>, T::Payload))
        requires
            self.id() == writer.id(),
        ensures
            out.0.is_init(),
            out.0.ptr() == self.ptr(),
            out.0.value().into_spec() == writer@,
            writer@.wf_payload(out.1),
        opens_invariants [self.namespace()]
    {
        use_type_invariant(&self);
        use_type_invariant(&writer);
        let tracked RWShared {
            inner: Tracked(inner),
            unique_ns: _,
        } = self;
        let tracked RWSharedInner { atom, payload_handle: handle } = inner;
        let tracked mut state = atom.into_inner();
        let tracked WritePerm { perm: writer_perm } = writer;
        state.value_frac.combine(writer_perm);
        let tracked payload = state.payload.into_payload(handle);
        let tracked RWState {
            perm,
            payload: _,
            value_frac: _,
            obs: _,
        } = state;
        (perm, payload)
    }
}

} // verus!

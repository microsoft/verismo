//! A payload slot, built on a tokenized state machine.
//!
//! This is the `--features state_machine` counterpart to `payload_slot.rs`. Both expose the same
//! four types with the same API; `tokens_impl/mod.rs` picks one with `#[path]`. The difference
//! is only in how the composition laws are established: `payload_slot.rs` proves them by hand
//! over a `SlotCarrier` PCM, this file has the `tokenized_state_machine!` macro derive them.
//!
//! ## How the types fit together
//!
//! ```text
//!                        PayloadHolder<P>          the writer's side
//!                        |  unpublished: Option<P>     the payload, while it is still private
//!                        |  slot: SlotOwner<P>     custody of the slot
//!                        v
//!            .-----------------------------.
//!            |          one slot           |
//!            '-----------------------------'
//!             |            |             |
//!    SlotOwner<P>    SlotHandle<P>   PayloadTicket<P>
//!    exclusive       exclusive       duplicable
//!    custody         the reader's    "payload p was in
//!    of the          right to look   the slot at version v"
//!    payload         inside
//!
//!    handle + ticket at the same version  ==>  &P, borrowed for the ticket's lifetime
//!    owner  + handle at the same version  ==>  the payload back, and the version bumps
//! ```
//!
//! Bumping the version on the way out is what makes every ticket handed out so far go stale, so a
//! reader cannot keep looking at a payload that has been reclaimed. Reclaiming needs the handle,
//! which by then is out in the world with the readers -- so it cannot happen behind their backs.
use verus_state_machines_macros::*;
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::modes::tracked_swap;

verus! {

/// What the slot's owner knows and controls: which version the slot is at, and what is in it.
///
/// `stored` is not redundant with the `payload` field. Transitions may not read a
/// `storage_option` field, so this is the only readable record of what the slot holds; the
/// `owner_knows_what_is_stored` invariant is what ties the record to reality. It is also what lets
/// `take` name the payload it is withdrawing.
#[verifier::accept_recursive_types(P)]
pub struct SlotStatus<P> {
    pub version: nat,
    pub stored: Option<P>,
}

} // verus!
// `accept_recursive_types(P)` because the real payload is recursive: it contains a
// `Seq<RWShared<..>>`, which contains payloads again.
tokenized_state_machine!(
    #[verifier::accept_recursive_types(P)]
    slot<P> {
        fields {
            /// Where the payload really lives. `storage_option` is what makes `guard` -- and so
            /// `SlotHandle::borrow` -- possible.
            #[sharding(storage_option)]
            pub payload: Option<P>,
            /// The owner's exclusive token.
            #[sharding(variable)]
            pub owner: SlotStatus<P>,
            /// The reader's exclusive token. Its exclusivity is what forces reclaiming to go
            /// through the reader.
            #[sharding(option)]
            pub handle: Option<nat>,
            /// Duplicable knowledge, no custody -- exactly what a ticket is.
            #[sharding(persistent_map)]
            pub tickets: Map<nat, P>,
        }

        #[invariant]
        pub fn handle_tracks_version(&self) -> bool {
            self.handle is Some ==> self.handle->Some_0 == self.owner.version
        }

        #[invariant]
        pub fn tickets_are_not_from_the_future(&self) -> bool {
            forall |v: nat| #[trigger] self.tickets.contains_key(v) ==> v <= self.owner.version
        }

        #[invariant]
        pub fn owner_knows_what_is_stored(&self) -> bool {
            &&& self.payload == self.owner.stored
            &&& (self.owner.stored is Some <==> self.tickets.contains_key(self.owner.version))
            &&& (self.owner.stored is Some
                    ==> self.tickets[self.owner.version] == self.owner.stored->Some_0)
        }

        init!{
            start() {
                init payload = Option::None;
                init owner = SlotStatus { version: 0, stored: Option::None };
                init handle = Option::Some(0);
                init tickets = Map::empty();
            }
        }

        #[inductive(start)]
        fn start_inductive(post: Self) {
        }

        /// A handle and a ticket naming the same version yield a shared reference to the payload.
        property!{
            borrow(v: nat, p: P) {
                have handle >= Some(v);
                have tickets >= [v => p];
                guard payload >= Some(p);
            }
        }

        /// The owner alone can see what is in the slot: it *is* custody, so it needs no ticket.
        /// The reference lives as long as the borrow of the owner token, and no longer.
        property!{
            borrow_owner(p: P) {
                require pre.owner.stored == Some(p);
                guard payload >= Some(p);
            }
        }

        transition!{
            put(p: P) {
                require pre.owner.stored is None;
                deposit payload += Some(p);
                update owner = SlotStatus { version: pre.owner.version, stored: Some(p) };
                // Persistent strategies take `(union)=`, not `+=`.
                add tickets (union)= [pre.owner.version => p];
            }
        }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, p: P) {
        }

        /// Another copy of the ticket for whatever is in the slot. Free: persistent tokens are
        /// duplicable, and this one is already accounted for.
        transition!{
            mint_ticket() {
                require pre.owner.stored is Some;
                add tickets (union)= [pre.owner.version => pre.owner.stored->Some_0];
            }
        }

        #[inductive(mint_ticket)]
        fn mint_ticket_inductive(pre: Self, post: Self) {
        }

        transition!{
            take() {
                require pre.owner.stored is Some;
                // Surrendering the handle *is* the rule that reclaiming needs the reader.
                remove handle -= Some(pre.owner.version);
                withdraw payload -= Some(pre.owner.stored->Some_0);
                update owner = SlotStatus {
                    version: (pre.owner.version + 1) as nat,
                    stored: Option::None,
                };
                add handle += Some((pre.owner.version + 1) as nat);
            }
        }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self) {
        }
    }
);

verus! {

/// Custody of a slot: it holds the payload, and the right to change what is in it.
///
/// Held by whoever may change the slot's contents -- in the reader/writer model, the state living
/// inside the atomic invariant.
pub tracked struct SlotOwner<P> {
    tracked inst: slot::Instance<P>,
    tracked tok: slot::owner<P>,
}

impl<P> SlotOwner<P> {
    /// Identifies which slot this is. All pieces of one slot share it.
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    /// The slot's version, which the handle must agree with.
    pub closed spec fn version(self) -> nat {
        self.tok.value().version
    }

    /// What is in the slot: `None` when it is empty.
    pub closed spec fn stored(self) -> Option<P> {
        self.tok.value().stored
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.tok.instance_id() == self.inst.id()
    }

    /// Creates a fresh, empty slot, splitting it into the owner's piece and the reader's handle.
    pub proof fn new() -> (tracked out: (SlotOwner<P>, SlotHandle<P>))
        ensures
            out.0.id() == out.1.id(),
            out.0.version() == 0,
            out.1.version() == 0,
            out.0.stored() is None,
    {
        let tracked (Tracked(inst), Tracked(owner_tok), Tracked(handle_tok), Tracked(_tickets)) =
            slot::Instance::<P>::start(None);
        let tracked handle = SlotHandle { inst: inst.clone(), tok: handle_tok.tracked_unwrap() };
        let tracked owner = SlotOwner { inst, tok: owner_tok };
        (owner, handle)
    }

    /// A throwaway owner of a brand-new empty slot. Used only as a placeholder when swapping a
    /// real owner out from behind a `&mut`.
    pub proof fn dummy() -> (tracked out: SlotOwner<P>) {
        SlotOwner::new().0
    }

    /// Looks at what is in the slot, for as long as the owner is borrowed. No ticket needed: the
    /// owner *is* custody. The reference dies with the borrow of the owner, so a caller holding
    /// the owner inside an atomic invariant cannot carry it out of the block.
    pub proof fn borrow<'a>(tracked &'a self) -> (tracked out: &'a P)
        requires
            self.stored() is Some,
        ensures
            *out == self.stored()->Some_0,
    {
        use_type_invariant(self);
        self.inst.borrow_owner(self.stored()->Some_0, &self.tok)
    }

    /// Hands out another copy of the ticket for whatever is currently in the slot. Free, because
    /// persistent tokens are duplicable.
    pub proof fn mint_ticket(tracked self) -> (tracked out: (SlotOwner<P>, PayloadTicket<P>))
        requires
            self.stored() is Some,
        ensures
            out.0.id() == self.id(),
            out.0.version() == self.version(),
            out.0.stored() == self.stored(),
            out.1.id() == self.id(),
            out.1.version() == self.version(),
            Some(out.1.payload()) == self.stored(),
    {
        use_type_invariant(&self);
        let tracked minted = self.inst.mint_ticket(&self.tok);
        (self, PayloadTicket { tok: minted })
    }

    /// Puts a payload into an empty slot, handing back a ticket for it.
    pub proof fn put(tracked self, tracked payload: P) -> (tracked out: (
        SlotOwner<P>,
        PayloadTicket<P>,
    ))
        requires
            self.stored() is None,
        ensures
            out.0.id() == self.id(),
            out.0.version() == self.version(),
            out.0.stored() == Some(payload),
            out.1.id() == self.id(),
            out.1.version() == self.version(),
            out.1.payload() == payload,
    {
        use_type_invariant(&self);
        let tracked SlotOwner { inst, mut tok } = self;
        let tracked minted = inst.put(payload, payload, &mut tok);
        (SlotOwner { inst, tok }, PayloadTicket { tok: minted })
    }

    /// Takes the payload back out, which needs the reader's handle surrendered too.
    ///
    /// The version is bumped in the process, so every ticket handed out so far stops granting
    /// access. A fresh owner and handle at the new version come back.
    pub proof fn take(tracked self, tracked handle: SlotHandle<P>) -> (tracked out: (
        SlotOwner<P>,
        SlotHandle<P>,
        P,
    ))
        requires
            self.id() == handle.id(),
            self.version() == handle.version(),
            self.stored() is Some,
        ensures
            out.0.id() == self.id(),
            out.1.id() == self.id(),
            out.0.version() == self.version() + 1,
            out.1.version() == self.version() + 1,
            out.0.stored() is None,
            Some(out.2) == self.stored(),
    {
        use_type_invariant(&self);
        use_type_invariant(&handle);
        let tracked SlotOwner { inst, mut tok } = self;
        let tracked SlotHandle { inst: _, tok: handle_tok } = handle;
        let tracked (Tracked(payload), Tracked(new_handle_tok)) = inst.take(&mut tok, handle_tok);
        let tracked handle = SlotHandle { inst: inst.clone(), tok: new_handle_tok };
        (SlotOwner { inst, tok }, handle, payload)
    }
}

/// The reader's right to look inside the slot.
///
/// Because reclaiming the payload consumes it, holding one is also what stops the writer taking
/// the payload back from under a reader.
pub tracked struct SlotHandle<P> {
    tracked inst: slot::Instance<P>,
    tracked tok: slot::handle<P>,
}

/// Duplicable proof that `payload` was in the slot at `version`.
///
/// A ticket alone proves nothing about the present; paired with a handle naming the same version,
/// it proves the payload is in the slot right now.
pub tracked struct PayloadTicket<P> {
    tracked tok: slot::tickets<P>,
}

impl<P> SlotHandle<P> {
    /// Identifies which slot this is. All pieces of one slot share it.
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    /// The version this handle is good for.
    pub closed spec fn version(self) -> nat {
        self.tok.value()
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.tok.instance_id() == self.inst.id()
    }

    /// **The point of this module.** A handle plus a ticket naming the same version yields a
    /// shared reference to the payload that lives as long as the *ticket* -- in particular, longer
    /// than any atomic-invariant block, which is what the reader/writer model needs.
    ///
    /// `'a: 's` lets the long-lived handle reference shorten to the ticket's lifetime.
    pub proof fn borrow<'a, 's>(
        tracked &'a self,
        tracked ticket: &'s PayloadTicket<P>,
    ) -> (tracked out: &'s P) where 'a: 's
        requires
            self.id() == ticket.id(),
            self.version() == ticket.version(),
        ensures
            out == ticket.payload(),
    {
        use_type_invariant(self);
        self.inst.borrow(self.version(), ticket.payload(), &self.tok, &ticket.tok)
    }
}

impl<P> PayloadTicket<P> {
    /// Identifies which slot this is. All pieces of one slot share it.
    pub closed spec fn id(self) -> InstanceId {
        self.tok.instance_id()
    }

    pub closed spec fn version(self) -> nat {
        self.tok.key()
    }

    /// The payload this ticket names.
    pub closed spec fn payload(self) -> P {
        self.tok.value()
    }

    /// Two tickets for the same slot and version name the same payload.
    ///
    /// This is what makes a published payload *one* payload: without it, `SlotHandle::borrow`
    /// only says each reader sees whatever its own ticket names, which is equally consistent
    /// with two readers of the same slot seeing different payloads.
    pub proof fn agree(tracked &self, tracked other: &PayloadTicket<P>)
        requires
            self.id() == other.id(),
            self.version() == other.version(),
        ensures
            self.payload() == other.payload(),
    {
        self.tok.agree(&other.tok);
    }
}

/// Where a payload lives: either held unpublished beside the value, or published into the slot.
///
/// The slot is created up front and stays put -- that is what keeps its identity and version
/// available at all times -- but starts empty, with the payload held unpublished alongside it. An
/// unpublished payload may be replaced as often as you like. Publishing moves it into the slot,
/// and is one-way: getting it back out requires the handle, which by then is out in the world
/// with the readers.
pub tracked struct PayloadHolder<P> {
    tracked unpublished: Option<P>,
    tracked slot: SlotOwner<P>,
}

impl<P> PayloadHolder<P> {
    /// Identifies the slot. Fixed for the lifetime of the holder.
    pub closed spec fn id(self) -> InstanceId {
        self.slot.id()
    }

    /// The slot's version. Fixed until the payload is reclaimed.
    pub closed spec fn version(self) -> nat {
        self.slot.version()
    }

    /// Whether the payload has been published into the slot, where readers reach it.
    pub closed spec fn is_published(self) -> bool {
        self.slot.stored() is Some
    }

    /// The payload, wherever it currently lives.
    pub closed spec fn payload(self) -> P {
        if self.unpublished is Some {
            self.unpublished->Some_0
        } else {
            self.slot.stored()->Some_0
        }
    }

    /// The payload is in exactly one place. Callers carry this rather than it being a type
    /// invariant, so that a holder can be swapped out from behind a `&mut` field.
    pub closed spec fn wf(self) -> bool {
        (self.unpublished is Some) == (self.slot.stored() is None)
    }

    /// Creates a holder for a payload that is not published yet, together with the handle a
    /// reader will need in order to look at it once it is.
    pub proof fn new(tracked payload: P) -> (tracked out: (PayloadHolder<P>, SlotHandle<P>))
        ensures
            out.0.id() == out.1.id(),
            out.0.version() == out.1.version(),
            !out.0.is_published(),
            out.0.payload() == payload,
            out.0.wf(),
    {
        let tracked (slot, handle) = SlotOwner::<P>::new();
        (PayloadHolder { unpublished: Some(payload), slot }, handle)
    }

    /// Swaps in a different payload, returning the old one. Only possible while the payload is
    /// still unpublished -- once published, it is there to stay.
    pub proof fn replace(tracked &mut self, tracked payload: P) -> (tracked out: P)
        requires
            old(self).wf(),
            !old(self).is_published(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).version() == old(self).version(),
            !final(self).is_published(),
            final(self).payload() == payload,
            out == old(self).payload(),
    {
        let tracked mut held = None;
        tracked_swap(&mut held, &mut self.unpublished);
        self.unpublished = Some(payload);
        held.tracked_unwrap()
    }

    /// Borrows the payload while it is still unpublished.
    ///
    /// **Usable only from inside an `open_atomic_invariant!` block.** The holder lives in the
    /// invariant, and this reference lives no longer than the borrow of the holder, so it dies
    /// when the block closes.
    ///
    /// What you get is *a* payload the current value is well-formed against, not *the* payload:
    /// the writer may `replace` it, so a later look may find a different one, and two threads are
    /// promised nothing in common. Publishing buys both of the things missing here -- a borrow
    /// that outlives the block, because the reference then draws its lifetime from the handle and
    /// ticket rather than the holder, and agreement between threads, because `agree` pins every
    /// ticket for one version to one payload.
    pub proof fn borrow_payload<'a>(tracked &'a self) -> (tracked out: &'a P)
        requires
            self.wf(),
        ensures
            *out == self.payload(),
    {
        if self.unpublished is Some {
            self.unpublished.tracked_borrow()
        } else {
            // The holder is well formed, so the payload must be in the slot.
            self.slot.borrow()
        }
    }

    /// Borrows the payload mutably, so it can be changed in place instead of `replace`d whole.
    /// Hand it back unchanged and the last clause says the holder is unchanged too.
    ///
    /// Only while the payload is unpublished. Once published, `SlotHandle::borrow` hands out
    /// `&P` whose lifetime comes from a ticket rather than from this borrow, so those references
    /// can still be live -- a `&mut` alongside them would be unsound. That is the same one-way
    /// step `replace` refuses, for the same reason.
    pub proof fn borrow_payload_mut<'a>(tracked &'a mut self) -> (tracked out: &'a mut P)
        requires
            old(self).wf(),
            !old(self).is_published(),
        ensures
            *out == old(self).payload(),
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).version() == old(self).version(),
            !final(self).is_published(),
            final(self).payload() == *final(out),
            (*final(out) == *out) ==> *final(self) == *old(self),
    {
        match self.unpublished {
            Some(ref mut payload) => payload,
            // Unreachable: `wf()` and not published put the payload here.
            None => proof_from_false(),
        }
    }

    /// Publishes the payload into the slot, where readers can reach it, and returns the first
    /// ticket for it. One-way until the reader's handle comes back: only `reclaim` undoes this,
    /// and it consumes the handle and bumps the version.
    pub proof fn publish(tracked &mut self) -> (tracked out: PayloadTicket<P>)
        requires
            old(self).wf(),
            !old(self).is_published(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).version() == old(self).version(),
            final(self).is_published(),
            final(self).payload() == old(self).payload(),
            out.id() == old(self).id(),
            out.version() == old(self).version(),
            out.payload() == old(self).payload(),
    {
        let tracked mut held = None;
        tracked_swap(&mut held, &mut self.unpublished);
        let tracked payload = held.tracked_unwrap();
        let tracked mut slot = SlotOwner::dummy();
        tracked_swap(&mut slot, &mut self.slot);
        let tracked (slot, ticket) = slot.put(payload);
        self.slot = slot;
        ticket
    }

    /// Hands out another ticket for an already-published payload.
    pub proof fn mint_ticket(tracked &mut self) -> (tracked out: PayloadTicket<P>)
        requires
            old(self).wf(),
            old(self).is_published(),
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).version() == old(self).version(),
            final(self).is_published(),
            final(self).payload() == old(self).payload(),
            out.id() == old(self).id(),
            out.version() == old(self).version(),
            out.payload() == old(self).payload(),
    {
        let tracked mut slot = SlotOwner::dummy();
        tracked_swap(&mut slot, &mut self.slot);
        let tracked (slot, ticket) = slot.mint_ticket();
        self.slot = slot;
        ticket
    }

    /// Takes a published payload back, which requires surrendering the reader's handle. The version
    /// is bumped, so every ticket handed out so far goes stale, and the payload becomes private
    /// again.
    pub proof fn reclaim(tracked self, tracked handle: SlotHandle<P>) -> (tracked out: (
        PayloadHolder<P>,
        SlotHandle<P>,
    ))
        requires
            self.wf(),
            self.is_published(),
            self.id() == handle.id(),
            self.version() == handle.version(),
        ensures
            out.0.wf(),
            out.0.id() == self.id(),
            out.1.id() == self.id(),
            out.0.version() == self.version() + 1,
            out.1.version() == self.version() + 1,
            !out.0.is_published(),
            out.0.payload() == self.payload(),
    {
        let tracked PayloadHolder { unpublished, slot } = self;
        let tracked (slot, handle, payload) = slot.take(handle);
        (PayloadHolder { unpublished: Some(payload), slot }, handle)
    }

    /// Consumes the holder and its reader handle, returning the payload wherever it currently is.
    ///
    /// A published payload is reclaimed first, which advances the slot version and invalidates
    /// every outstanding ticket before the payload is removed from the private holder.
    pub proof fn into_payload(tracked self, tracked handle: SlotHandle<P>) -> (tracked out: P)
        requires
            self.wf(),
            self.id() == handle.id(),
            self.version() == handle.version(),
        ensures
            out == self.payload(),
    {
        if self.is_published() {
            let tracked (holder, _handle) = self.reclaim(handle);
            let tracked PayloadHolder { unpublished, slot: _ } = holder;
            unpublished.tracked_unwrap()
        } else {
            let tracked PayloadHolder { unpublished, slot: _ } = self;
            unpublished.tracked_unwrap()
        }
    }
}

} // verus!

//! A payload slot: a place attached to a cell holding one tracked payload, which readers may
//! look at concurrently and lock-free.
//!
//! A **ticket** is duplicable knowledge that a payload was in the slot at some **version**; a
//! **handle** says what the version is now. Together they prove the payload is in the slot right
//! now, which is what `borrow` turns into a shared reference outliving the atomic-invariant block
//! it came from. That is impossible with an `AtomicInvariant` alone, hence `StorageResource`.
//!
//! The owner and the handle hold one half each of the version claim, so taking the payload back
//! needs the reader token. Doing so bumps the version, retiring every ticket at once.
//!
//! `SlotCarrier` is the ghost algebra and the only place a rule is written down. `SlotOwner`,
//! `SlotHandle` and `PayloadTicket` are thin token wrappers over pieces of one `SlotResource`.
//! Each is one carrier shape, and two equations between those shapes drive everything:
//!
//! ```text
//!   token           carrier shape   carries                     lives in
//!   -----           -------------   -------                     --------
//!   SlotOwner       owner_piece     claim half + the payload    the cell's atomic invariant
//!   SlotHandle      handle_piece    claim half                  the reader token
//!   PayloadTicket   ticket_piece    knowledge, duplicable       any reader, freely copied
//!
//!   owner_piece  op  handle_piece  ==  whole
//!       the only shape `rel` accepts, so only these two together can change what is stored
//!       -- which is why reclaiming the payload costs the reader token
//!
//!   handle_piece op  ticket_piece  ==  reader_piece
//!       what `guards` the payload, so a reader needs both: the ticket says which payload,
//!       the handle says the version has not moved on
//! ```
//!
//! `PayloadHolder` sits on top, keeping a payload either unpublished, where it may be replaced,
//! or published into the slot, where it is permanent.

#[cfg(verus_only)]
use vstd::modes::tracked_swap;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::storage_protocol::{deposits, guards, incl, withdraws};
use vstd::resource::storage_protocol::{Protocol, StorageResource};
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

/// The ghost algebra behind a payload slot. Only all the pieces together make a `Piece` holding
/// both the owner and the handle, which is the one shape `rel` accepts.
///
/// The version claim has two named holders rather than a count of shares, and `op` rejects a
/// second of either. That the two name the *same* version is left to `rel`, which keeps `op`
/// free of version logic.
#[verifier::accept_recursive_types(P)]
pub enum SlotCarrier<P> {
    /// The neutral piece: contributes nothing.
    Unit,
    /// Two pieces that cannot coexist were composed (e.g. two owners of the same slot).
    Invalid,
    Piece {
        /// The slot's owner: the version it claims, and the payload in the slot (`None` when the
        /// slot is empty). Exclusive -- a slot has one owner.
        owner: Option<(nat, Option<P>)>,
        /// The reader handle's claim on the version. Exclusive.
        handle: Option<nat>,
        /// Duplicable knowledge: "this payload was in the slot at this version".
        /// Composition unions these, so a ticket can be handed out over and over.
        tickets: Set<(nat, P)>,
    },
}

impl<P> SlotCarrier<P> {
    /// A piece that carries nothing but a single ticket, and so no version claim at all.
    pub open spec fn ticket_piece(version: nat, payload: P) -> Self {
        SlotCarrier::Piece { owner: None, handle: None, tickets: set![(version, payload)] }
    }

    /// The piece held by the slot's owner: custody of the payload, and its half of the claim.
    pub open spec fn owner_piece(version: nat, stored: Option<P>, tickets: Set<(nat, P)>) -> Self {
        SlotCarrier::Piece { owner: Some((version, stored)), handle: None, tickets }
    }

    /// The piece held by the reader token: one half of the version claim, and nothing else.
    pub open spec fn handle_piece(version: nat) -> Self {
        SlotCarrier::Piece { owner: None, handle: Some(version), tickets: Set::empty() }
    }

    /// What a reader actually presents in order to look inside the slot: its handle together with
    /// a ticket. This is `handle_piece(version)` composed with `ticket_piece(version, payload)`.
    pub open spec fn reader_piece(version: nat, payload: P) -> Self {
        SlotCarrier::Piece {
            owner: None,
            handle: Some(version),
            tickets: set![(version, payload)],
        }
    }

    /// Every piece of a slot composed together: the owner and the handle, both naming the same
    /// version. This is the only shape `rel` accepts.
    pub open spec fn whole(version: nat, stored: Option<P>, tickets: Set<(nat, P)>) -> Self {
        SlotCarrier::Piece {
            owner: Some((version, stored)),
            handle: Some(version),
            tickets,
        }
    }
}

/// Pick whichever side carries the value. `op` only reaches this when at most one side is `Some`.
pub open spec fn comb_opt<T>(a: Option<T>, b: Option<T>) -> Option<T> {
    match a {
        Some(_) => a,
        None => b,
    }
}

/// Tickets say one thing per version: a slot holds one payload at a time, so two tickets naming
/// the same version name the same payload. `rel` demands this of a complete slot, which is what
/// makes [`PayloadTicket::agree`] provable even for versions the slot has already left behind.
pub open spec fn tickets_functional<P>(tickets: Set<(nat, P)>) -> bool {
    forall|v: nat, p1: P, p2: P|
        #![trigger tickets.contains((v, p1)), tickets.contains((v, p2))]
        tickets.contains((v, p1)) && tickets.contains((v, p2)) ==> p1 == p2
}

/// A piece included in a valid whole contributes its ticket to that whole.
pub proof fn lemma_ticket_incl<P>(version: nat, payload: P, whole: SlotCarrier<P>)
    requires
        incl(SlotCarrier::ticket_piece(version, payload), whole),
        whole is Piece,
    ensures
        whole->tickets.contains((version, payload)),
{
    let piece = SlotCarrier::<P>::ticket_piece(version, payload);
    let rest = choose|rest: SlotCarrier<P>| #[trigger] piece.op(rest) == whole;
    assert(piece.op(rest) == whole);
    if let SlotCarrier::Piece { tickets: t2, .. } = rest {
        assert(set![(version, payload)].union(t2).contains((version, payload)));
    }
}

impl<P> Protocol<nat, P> for SlotCarrier<P> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (SlotCarrier::Unit, _) => other,
            (_, SlotCarrier::Unit) => self,
            (SlotCarrier::Invalid, _) => SlotCarrier::Invalid,
            (_, SlotCarrier::Invalid) => SlotCarrier::Invalid,
            (
                SlotCarrier::Piece { owner: o1, handle: h1, tickets: t1 },
                SlotCarrier::Piece { owner: o2, handle: h2, tickets: t2 },
            ) => {
                // A slot has exactly one owner and one handle. Tickets just accumulate.
                if (o1 is Some && o2 is Some) || (h1 is Some && h2 is Some) {
                    SlotCarrier::Invalid
                } else {
                    SlotCarrier::Piece {
                        owner: comb_opt(o1, o2),
                        handle: comb_opt(h1, h2),
                        tickets: t1.union(t2),
                    }
                }
            },
        }
    }

    /// Ties the ghost state to the payload really held in storage. Only a *whole* slot -- an
    /// owner and a handle together -- says anything about storage.
    open spec fn rel(self, s: IMap<nat, P>) -> bool {
        match self {
            SlotCarrier::Piece {
                owner: Some((version, stored)),
                handle: Some(claimed),
                tickets,
            } => {
                // Both holders of the version claim agree on it.
                &&& claimed == version
                // Storage holds the payload under the slot's current version, and nothing else.
                &&& match stored {
                    Some(p) => s =~= imap![version => p],
                    None => s =~= imap![],
                }
                // No ticket may claim a version the slot has not reached yet.
                &&& forall|x: (nat, P)| #[trigger] tickets.contains(x) ==> x.0 <= version
                // A ticket for the *current* version tells the truth: that payload really is in
                // the slot. Bumping the version is therefore what retires old tickets -- they stay
                // true about the past but stop constraining the present.
                &&& forall|x: (nat, P)| #[trigger] tickets.contains(x) && x.0 == version
                    ==> stored == Some(x.1)
                &&& tickets_functional(tickets)
            },
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        SlotCarrier::Unit
    }

    proof fn commutative(a: Self, b: Self) {
        if let (
            SlotCarrier::Piece { tickets: t1, .. },
            SlotCarrier::Piece { tickets: t2, .. },
        ) = (a, b) {
            assert(t1.union(t2) =~= t2.union(t1));
        }
        assert(Self::op(a, b) =~= Self::op(b, a));
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        if let (
            SlotCarrier::Piece { tickets: t1, .. },
            SlotCarrier::Piece { tickets: t2, .. },
            SlotCarrier::Piece { tickets: t3, .. },
        ) = (a, b, c) {
            assert(t1.union(t2).union(t3) =~= t1.union(t2.union(t3)));
        }
        assert(Self::op(a, Self::op(b, c)) =~= Self::op(Self::op(a, b), c));
    }

    proof fn op_unit(a: Self) {
    }
}

/// **Borrow.** A handle plus a ticket for the version it names sees the payload, whatever else
/// is going on. `guards` is what `StorageResource::guard` turns into a reference outliving the
/// atomic-invariant block, which is the point of the module.
///
/// The handle's half of the claim forces any completion to name the same version, and `rel` says
/// a ticket for the current version is truthful.
pub proof fn lemma_borrow<P>(version: nat, payload: P)
    ensures
        guards::<nat, P, SlotCarrier<P>>(
            SlotCarrier::reader_piece(version, payload),
            imap![version => payload],
        ),
{
    let p = SlotCarrier::<P>::reader_piece(version, payload);
    assert forall|q: SlotCarrier<P>, t: IMap<nat, P>| #![all_triggers]
        SlotCarrier::rel(SlotCarrier::op(p, q), t) implies imap![version => payload].submap_of(
        t,
    ) by {
        broadcast use vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas;

        let whole = SlotCarrier::op(p, q);
        // The reader's half of the claim fixes the version, and `rel` makes the owner agree.
        assert(whole->owner->Some_0.0 == version);
        // The reader's ticket survives composition, and at the current version it cannot lie.
        assert(whole->tickets.contains((version, payload)));
        assert(whole->owner->Some_0.1 == Some(payload));
        assert(t =~= imap![version => payload]);
    }
}

/// **Borrow, owner side.** The owner piece is custody, so it sees the slot without a ticket and
/// needs nothing from anyone else. This is how the state inside the atomic invariant reads a
/// payload it has published, for as long as the block lasts.
pub proof fn lemma_borrow_owner<P>(version: nat, payload: P, tickets: Set<(nat, P)>)
    ensures
        guards::<nat, P, SlotCarrier<P>>(
            SlotCarrier::owner_piece(version, Some(payload), tickets),
            imap![version => payload],
        ),
{
    let p = SlotCarrier::<P>::owner_piece(version, Some(payload), tickets);
    assert forall|q: SlotCarrier<P>, t: IMap<nat, P>| #![all_triggers]
        SlotCarrier::rel(SlotCarrier::op(p, q), t) implies imap![version => payload].submap_of(
        t,
    ) by {
        broadcast use vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas;
        // Only one piece may hold custody, so the owner's view of the slot is the whole's.
        let whole = SlotCarrier::op(p, q);
        assert(whole->owner == Some((version, Some(payload))));
        assert(t =~= imap![version => payload]);
    }
}

/// **Put.** The slot's owner may place a payload into an empty slot, and in doing so mints a
/// ticket recording that the payload was there at this version.
///
/// The owner can do this alone -- no handle needed -- because it already holds a version claim, so
/// it knows which version the ticket should name.
pub proof fn lemma_put<P>(version: nat, payload: P, tickets: Set<(nat, P)>)
    ensures
        deposits::<nat, P, SlotCarrier<P>>(
            SlotCarrier::owner_piece(version, None, tickets),
            imap![version => payload],
            SlotCarrier::owner_piece(version, Some(payload), tickets.insert((version, payload))),
        ),
{
    let p1 = SlotCarrier::<P>::owner_piece(version, None, tickets);
    let p2 = SlotCarrier::<P>::owner_piece(
        version,
        Some(payload),
        tickets.insert((version, payload)),
    );
    let b1 = imap![version => payload];
    assert forall|q: SlotCarrier<P>, t1: IMap<nat, P>| #![all_triggers]
        SlotCarrier::rel(SlotCarrier::op(p1, q), t1) implies {
        &&& SlotCarrier::rel(SlotCarrier::op(p2, q), t1.union_prefer_right(b1))
        &&& t1.dom().disjoint(b1.dom())
    } by {
        broadcast use vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas;

        let all = SlotCarrier::op(p1, q)->tickets;
        let all2 = SlotCarrier::op(p2, q)->tickets;
        assert(all2 =~= all.insert((version, payload)));
        // The slot is empty, so `rel` guarantees nobody holds a ticket for this version yet --
        // which is exactly what makes minting a new one safe.
        assert forall|x: (nat, P)| #[trigger] all.contains(x) implies x.0 < version by {
            assert(x.0 <= version);
        }
        assert(tickets_functional(all2));
        assert(t1 =~= imap![]);
        assert(t1.union_prefer_right(b1) =~= b1);
        assert(t1.dom() =~= ISet::empty());
    }
}

/// **Take.** The owner and the handle together -- in practice, the reader token -- take the
/// payload back out, bumping the version as it leaves.
///
/// That one step retires every ticket: each names a version at most the old one, so none names
/// the new one and `rel` stops requiring anything of them. They stay true about the past.
pub proof fn lemma_take<P>(version: nat, payload: P, tickets: Set<(nat, P)>)
    ensures
        withdraws::<nat, P, SlotCarrier<P>>(
            SlotCarrier::whole(version, Some(payload), tickets),
            SlotCarrier::whole((version + 1) as nat, None, tickets),
            imap![version => payload],
        ),
{
    let p1 = SlotCarrier::<P>::whole(version, Some(payload), tickets);
    let p2 = SlotCarrier::<P>::whole((version + 1) as nat, None, tickets);
    let b2 = imap![version => payload];
    assert forall|q: SlotCarrier<P>, t1: IMap<nat, P>| #![all_triggers]
        SlotCarrier::rel(SlotCarrier::op(p1, q), t1) implies {
        &&& SlotCarrier::rel(SlotCarrier::op(p2, q), t1.remove_keys(b2.dom()))
        &&& b2.submap_of(t1)
    } by {
        broadcast use vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas;

        if q is Piece {
            // `p1` is already a whole slot, so any completion holds neither the owner nor the
            // handle, and therefore cannot object to the version being bumped.
            assert(q->owner is None);
            assert(q->handle is None);
            assert(SlotCarrier::op(p2, q) == SlotCarrier::<P>::whole(
                (version + 1) as nat,
                None,
                tickets.union(q->tickets),
            ));
            assert(tickets.union(q->tickets) =~= SlotCarrier::op(p1, q)->tickets);
        } else {
            assert(SlotCarrier::op(p2, q) == p2);
            assert(SlotCarrier::op(p1, q) == p1);
        }
        assert(t1 =~= b2);
        assert(t1.remove_keys(b2.dom()) =~= IMap::<nat, P>::empty());
    }
}

/// A fresh, empty slot is a legitimate starting state, with no payload in storage.
pub proof fn lemma_empty_slot<P>()
    ensures
        SlotCarrier::<P>::rel(SlotCarrier::whole(0, None, Set::empty()), IMap::empty()),
{
    broadcast use vstd::imap::group_imap_lemmas;

}

/// Handing out a ticket costs nothing: composing the owner's piece with a copy of a ticket it
/// already accounts for gives back the very same piece. That idempotence is what lets the same
/// ticket be handed to reader after reader.
pub proof fn lemma_ticket_is_free<P>(
    version: nat,
    stored: Option<P>,
    tickets: Set<(nat, P)>,
    v: nat,
    p: P,
)
    requires
        tickets.contains((v, p)),
    ensures
        SlotCarrier::op(
            SlotCarrier::owner_piece(version, stored, tickets),
            SlotCarrier::ticket_piece(v, p),
        ) == SlotCarrier::<P>::owner_piece(version, stored, tickets),
{
    assert(tickets.union(set![(v, p)]) =~= tickets);
}

/// A reader's handle and a ticket, held separately, can always be viewed as the combined piece
/// they make up -- even when embedded in a larger composition. This is the bookkeeping step that
/// lets `borrow` reach `lemma_borrow`.
pub proof fn lemma_reader_piece_included<P>(version: nat, payload: P, j: SlotCarrier<P>)
    requires
        incl(SlotCarrier::<P>::handle_piece(version), j),
        incl(SlotCarrier::<P>::ticket_piece(version, payload), j),
    ensures
        incl(SlotCarrier::<P>::reader_piece(version, payload), j),
{
    let handle = SlotCarrier::<P>::handle_piece(version);
    let ticket = SlotCarrier::<P>::ticket_piece(version, payload);
    let reader = SlotCarrier::<P>::reader_piece(version, payload);
    let c = choose|c| SlotCarrier::op(handle, c) == j;
    let d = choose|d| SlotCarrier::op(ticket, d) == j;
    assert(SlotCarrier::op(handle, c) == j);
    assert(SlotCarrier::op(ticket, d) == j);
    if j is Piece {
        // `j` already carries this ticket, so composing it in again changes nothing.
        assert(j->tickets.contains((version, payload))) by {
            assert(set![(version, payload)].union(d->tickets) =~= j->tickets);
        }
        assert(SlotCarrier::op(ticket, j) == j) by {
            assert(set![(version, payload)].union(j->tickets) =~= j->tickets);
        }
        assert(SlotCarrier::op(ticket, handle) == reader) by {
            assert(set![(version, payload)].union(Set::empty()) =~= set![(version, payload)]);
        }
        SlotCarrier::<P>::associative(ticket, handle, c);
        assert(SlotCarrier::op(reader, c) == j);
    } else {
        // `j` cannot be the unit (a handle contributes something), so it is `Invalid`, which
        // everything is included in.
        assert(j is Invalid);
        assert(SlotCarrier::op(reader, SlotCarrier::Invalid) == j);
    }
}

/// The raw resource behind every slot token.
pub type SlotResource<P> = StorageResource<nat, P, SlotCarrier<P>>;

/// Custody of a slot: it holds the payload, and one half of the version claim.
///
/// Held by whoever is allowed to change what is in the slot -- in the reader/writer model, the
/// state living inside the atomic invariant.
pub tracked struct SlotOwner<P> {
    tracked res: SlotResource<P>,
    ghost tickets: Set<(nat, P)>,
    ghost version: nat,
    ghost stored: Option<P>,
}

/// The other half of the version claim, held by the reader token itself.
///
/// It is what lets a reader look inside the slot, and -- because taking the payload back needs
/// both halves -- what makes reclaiming the payload require the reader token.
pub tracked struct SlotHandle<P> {
    tracked res: SlotResource<P>,
    ghost version: nat,
}

/// Duplicable proof that `payload` was in the slot at `version`.
///
/// A ticket alone proves nothing about the present; paired with a handle naming the same version,
/// it proves the payload is in the slot right now.
pub tracked struct PayloadTicket<P> {
    tracked res: SlotResource<P>,
    ghost version: nat,
    ghost payload: P,
}

impl<P> SlotOwner<P> {
    /// Identifies which slot this is. All pieces of one slot share it.
    pub closed spec fn id(self) -> Loc {
        self.res.loc()
    }

    /// The slot's version, which the handle must agree with.
    pub closed spec fn version(self) -> nat {
        self.version
    }

    /// What is in the slot: `None` when it is empty.
    pub closed spec fn stored(self) -> Option<P> {
        self.stored
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        &&& self.res.value() == SlotCarrier::owner_piece(self.version, self.stored, self.tickets)
        // A ticket for whatever is currently stored has always already been minted, which is what
        // makes handing out further copies of it free.
        &&& self.stored is Some ==> self.tickets.contains((self.version, self.stored->Some_0))
    }

    /// Creates a fresh, empty slot, splitting it into the owner's piece and the reader's handle.
    pub proof fn new() -> (tracked out: (SlotOwner<P>, SlotHandle<P>))
        ensures
            out.0.id() == out.1.id(),
            out.0.version() == 0,
            out.1.version() == 0,
            out.0.stored() is None,
    {
        lemma_empty_slot::<P>();
        let tracked res = SlotResource::alloc(
            SlotCarrier::whole(0, None, Set::empty()),
            IMap::tracked_empty(),
        );
        assert(Set::<(nat, P)>::empty().union(Set::empty()) =~= Set::empty());
        let tracked (owner_res, handle_res) = res.split(
            SlotCarrier::owner_piece(0, None, Set::empty()),
            SlotCarrier::handle_piece(0),
        );
        (
            SlotOwner { res: owner_res, tickets: Set::empty(), version: 0, stored: None },
            SlotHandle { res: handle_res, version: 0 },
        )
    }

    /// A throwaway owner of a brand-new empty slot. Used only as a placeholder when swapping a
    /// real owner out from behind a `&mut`.
    pub proof fn dummy() -> (tracked out: SlotOwner<P>) {
        SlotOwner::new().0
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
        let tracked SlotOwner { res, tickets, version, stored } = self;
        let tracked mut base = IMap::tracked_empty();
        base.tracked_insert(version, payload);
        assert(base =~= imap![version => payload]);
        lemma_put(version, payload, tickets);
        let tracked res = res.deposit(
            base,
            SlotCarrier::owner_piece(version, Some(payload), tickets.insert((version, payload))),
        );
        let tracked owner = SlotOwner {
            res,
            tickets: tickets.insert((version, payload)),
            version,
            stored: Some(payload),
        };
        owner.mint_ticket()
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
        let payload = self.stored->Some_0;
        lemma_borrow_owner(self.version, payload, self.tickets);
        let tracked base = SlotResource::guard(&self.res, imap![self.version => payload]);
        base.tracked_borrow(self.version)
    }

    /// Hands out another copy of the ticket for whatever is currently in the slot. Free, because
    /// the ticket is already accounted for in the owner's piece.
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
        let tracked SlotOwner { res, tickets, version, stored } = self;
        let payload = stored->Some_0;
        lemma_ticket_is_free(version, stored, tickets, version, payload);
        let tracked (res, ticket_res) = res.split(
            SlotCarrier::owner_piece(version, stored, tickets),
            SlotCarrier::ticket_piece(version, payload),
        );
        (
            SlotOwner { res, tickets, version, stored },
            PayloadTicket { res: ticket_res, version, payload },
        )
    }

    /// Takes the payload back out, which needs both halves of the version claim -- so the reader's
    /// handle must be surrendered too.
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
        let tracked SlotOwner { res, tickets, version, stored } = self;
        let tracked SlotHandle { res: handle_res, version: _ } = handle;
        let payload = stored->Some_0;
        assert(tickets.union(Set::empty()) =~= tickets);
        let tracked res = SlotResource::join(res, handle_res);
        lemma_take(version, payload, tickets);
        let tracked (res, mut base) = res.withdraw(
            SlotCarrier::whole((version + 1) as nat, None, tickets),
            imap![version => payload],
        );
        let tracked payload = base.tracked_remove(version);
        let new_version = (version + 1) as nat;
        assert(tickets.union(Set::empty()) =~= tickets);
        let tracked (res, handle_res) = res.split(
            SlotCarrier::owner_piece(new_version, None, tickets),
            SlotCarrier::handle_piece(new_version),
        );
        (
            SlotOwner { res, tickets, version: new_version, stored: None },
            SlotHandle { res: handle_res, version: new_version },
            payload,
        )
    }
}

impl<P> SlotHandle<P> {
    pub closed spec fn id(self) -> Loc {
        self.res.loc()
    }

    pub closed spec fn version(self) -> nat {
        self.version
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.res.value() == SlotCarrier::<P>::handle_piece(self.version)
    }

    /// **The point of this module.** A handle plus a ticket naming the same version yields a
    /// shared reference to the payload that lives as long as the ticket -- in particular, longer
    /// than any atomic-invariant block.
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
        use_type_invariant(ticket);
        let version = self.version;
        let payload = ticket.payload;
        assert(IMap::<nat, P>::empty().union_prefer_right(imap![version => payload])
            =~= imap![version => payload]);
        let tracked joined = self.res.join_shared(&ticket.res);
        lemma_reader_piece_included(version, payload, joined.value());
        let tracked reader = joined.weaken(SlotCarrier::reader_piece(version, payload));
        lemma_borrow(version, payload);
        let tracked base = SlotResource::guard(reader, imap![version => payload]);
        base.tracked_borrow(version)
    }
}

impl<P> PayloadTicket<P> {
    pub closed spec fn id(self) -> Loc {
        self.res.loc()
    }

    pub closed spec fn version(self) -> nat {
        self.version
    }

    /// The payload this ticket names.
    pub closed spec fn payload(self) -> P {
        self.payload
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
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked joined = self.res.join_shared(&other.res);
        // `validate` hands back a frame that completes the joined value into something `rel`
        // accepts, and `rel` only accepts a `Piece`. So both tickets sit inside a valid whole.
        let ghost (frame, storage) = joined.validate();
        let ghost whole = joined.value().op(frame);
        assert(SlotCarrier::rel(whole, storage));
        assert(incl(SlotCarrier::ticket_piece(self.version, self.payload), whole)) by {
            SlotCarrier::<P>::associative(
                SlotCarrier::ticket_piece(self.version, self.payload),
                choose|c: SlotCarrier<P>| #[trigger]
                    SlotCarrier::ticket_piece(self.version, self.payload).op(c) == joined.value(),
                frame,
            );
        }
        assert(incl(SlotCarrier::ticket_piece(other.version, other.payload), whole)) by {
            SlotCarrier::<P>::associative(
                SlotCarrier::ticket_piece(other.version, other.payload),
                choose|c: SlotCarrier<P>| #[trigger]
                    SlotCarrier::ticket_piece(other.version, other.payload).op(c) == joined.value(),
                frame,
            );
        }
        lemma_ticket_incl(self.version, self.payload, whole);
        lemma_ticket_incl(other.version, other.payload, whole);
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.res.value() == SlotCarrier::ticket_piece(self.version, self.payload)
    }
}

/// Where a payload lives: unpublished beside the value, or published into the slot.
///
/// The slot is created up front and stays put, so its identity and version are always available,
/// but starts empty. An unpublished payload may be replaced freely. Publishing is one-way:
/// getting it back out needs the handle, which by then is out with the readers.
pub tracked struct PayloadHolder<P> {
    tracked unpublished: Option<P>,
    tracked slot: SlotOwner<P>,
}

impl<P> PayloadHolder<P> {
    /// Identifies the slot. Fixed for the lifetime of the holder.
    pub closed spec fn id(self) -> Loc {
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

    /// Borrows the payload, published or not. The reference dies with the borrow of the holder,
    /// so this is only usable inside an `open_atomic_invariant!` block -- which is why publishing
    /// still matters, `SlotHandle::borrow` drawing its lifetime from a ticket instead.
    ///
    /// Unpublished, this gives *a* payload the value is well-formed against, not *the* payload:
    /// the writer may `replace` it, and two threads are promised nothing in common. Publishing
    /// fixes it for the version, and `agree` pins every ticket for that version to it.
    pub proof fn borrow_payload<'a>(tracked &'a self) -> (tracked out: &'a P)
        requires
            self.wf(),
        ensures
            *out == self.payload(),
    {
        if self.unpublished is Some {
            self.unpublished.tracked_borrow()
        } else {
            self.slot.borrow()
        }
    }

    /// Borrows the payload mutably, to change it in place instead of `replace`ing it whole.
    /// Hand it back unchanged and the last clause says the holder is unchanged too.
    ///
    /// Unpublished only. Once published, references handed out by `SlotHandle::borrow` outlive
    /// this borrow, so a `&mut` alongside them would be unsound -- the same reason `replace`
    /// refuses.
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

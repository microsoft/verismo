// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//! Fractional ownership of a tracked value, verified with a tokenized state machine.
//!
//! Adapted from `verification/verify_proof/src/frac_perm.rs` in coconut-svsm
//! (<https://github.com/coconut-svsm/svsm>). Two changes from the original:
//!
//! * A share is a `real` rather than a `nat`, and the whole is fixed at `1`. A reader token is
//!   halved on every read, without bound, so shares have to be infinitely divisible; `nat` shares
//!   out of a fixed total cannot do that. With the whole fixed at `1`, `shares()` is directly the
//!   fraction held.
//! * A [`FracGhost<T>`] wrapper is added on top, matching the API of
//!   `vstd::resource::frac::FracGhost` so it can stand in for it.
//!
//! Two layers:
//!
//! * [`FracPerm<T>`] holds a *tracked* `T`. Because the value is really there, [`FracPerm::borrow`]
//!   can hand out a `&T` that any share-holder may read.
//! * [`FracGhost<T>`] is a `FracPerm<Ghost<T>>`, so its value is pure ghost data. There is nothing
//!   to borrow; holders just read `@`. Use this one where you would have used vstd's `FracGhost`.
//!
//! The invariant that makes it all work: the shares of all live tokens sum to exactly `1`, and
//! every share is positive. So one token holding the full `1` is the sole owner and may change
//! the value, while any smaller share only proves that the value it saw is the current one.
use verus_state_machines_macros::*;
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::modes::tracked_swap;
#[cfg(verus_only)]
use vstd::multiset::*;

tokenized_state_machine!(frac_inner<Perm> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        #[sharding(multiset)]
        pub reader: Multiset<(Option<Perm>, real)>, // read token and its share
    }

    #[invariant]
    pub fn frac_positive(&self) -> bool {
        forall |s| #[trigger] self.reader.count(s) > 0 ==> s.1 > 0.0real
    }

    #[invariant]
    pub fn shares_make_up_the_whole(&self) -> bool {
        sum(self.reader) == 1.0real
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |v| #[trigger] self.reader.count(v) > 0 ==> self.storage == v.0
    }

    #[invariant]
    pub fn no_share_exceeds_the_whole(&self) -> bool {
        forall |v| #[trigger] self.reader.count(v) > 0 ==> v.1 <= 1.0real
    }

    init!{
        initialize_once() {
            init storage = Option::None;
            init reader = Multiset::empty().insert((Option::None, 1.0real));
        }
    }

    #[inductive(initialize_once)]
    fn initialize_once_inductive(post: Self) {
        let frac = Multiset::empty().insert((Option::<Perm>::None, 1.0real));
        lemma_sum_remove(frac, (Option::None, 1.0real));
    }

    property! {
        is_same(p1: (Option<Perm>, real), p2: (Option<Perm>, real)) {
            have reader >= {p1};
            have reader >= {p2};
            birds_eye let r1 = pre.reader.contains(p1);
            birds_eye let r2 = pre.reader.contains(p2);
            assert p1.0 == p2.0;
        }
    }

    property! {
        share_is_at_most_the_whole(p: (Option<Perm>, real)) {
            have reader >= {p};
            birds_eye let r1 = pre.reader.contains(p);
            assert p.1 <= 1.0real;
        }
    }

    property! {
        shares_positive(p: (Option<Perm>, real)) {
            have reader >= {p};
            assert p.1 > 0.0real;
        }
    }

    // Two tokens of this instance hold shares that together are at most the whole.
    //
    // A `property!` cannot state this: two *borrowed* tokens carrying the same element are
    // indistinguishable from one borrowed twice, so nothing rules out double-counting a single
    // token. Removing one of them settles it -- `remove` plus `have` requires the multiset to
    // contain both occurrences -- and adding it straight back leaves the state unchanged. Hence a
    // transition rather than a property, and hence one token by value and one by reference.
    transition! {
        two_shares_bounded(p1: (Option<Perm>, real), p2: (Option<Perm>, real)) {
            remove reader -= {p1};
            have reader >= {p2};
            assert p1.1 + p2.1 <= 1.0real by {
                lemma_sum_remove(pre.reader, p1);
                lemma_sum_remove(pre.reader.remove(p1), p2);
                let rest = pre.reader.remove(p1).remove(p2);
                assert forall|e: (Option<Perm>, real)| #[trigger]
                    rest.count(e) > 0 implies e.count() > 0.0real by {
                    assert(pre.reader.count(e) > 0);
                }
                lemma_sum_positive(rest);
            };
            add reader += {p1};
        }
    }

    #[inductive(two_shares_bounded)]
    fn two_shares_bounded_inductive(
        pre: Self,
        post: Self,
        p1: (Option<Perm>, real),
        p2: (Option<Perm>, real),
    ) {
        lemma_sum_remove(pre.reader, p1);
        lemma_sum_insert(pre.reader.remove(p1), p1);
        assert(pre.reader.remove(p1).insert(p1) =~= pre.reader);
    }

    property! {
        reader_guard(x: Option<Perm>, shares: real) {
            require x.is_some();
            have reader >= {(x, shares)};
            guard storage >= Some(x.unwrap());
        }
    }

    transition! {
        do_share(x: Option<Perm>, shares: real, new_shares: real) {
            remove reader -= {(x, shares)};
            require(0.0real < new_shares < shares);
            add reader += {(x, new_shares)};
            add reader += {(x, shares - new_shares)};
        }
    }


    #[inductive(do_share)]
    fn do_share_inductive(pre: Self, post: Self, x: Option<Perm>, shares: real, new_shares: real) {
        let reader1 = pre.reader.remove((x, shares));
        let reader2 = reader1.insert((x, new_shares));
        lemma_sum_remove(pre.reader, (x, shares));
        lemma_sum_insert(reader1, (x, new_shares));
        lemma_sum_insert(reader2, (x, shares - new_shares));
    }

    transition! {
        take(x: Option<Perm>) {
            remove reader -= {(x, 1.0real)};
            require x.is_some();
            add reader += {(None, 1.0real)};
            withdraw storage -= Some(x.unwrap());
        }
    }

    #[inductive(take)]
    fn take_inductive(pre: Self, post: Self, x: Option<Perm>) {
        lemma_sum_remove(pre.reader, (x, 1.0real));
        let reader1 = pre.reader.remove((x, 1.0real));
        assert(reader1.len() == 0) by {
            lemma_sum_positive(reader1);
        }
        lemma_sum_insert(reader1, (None, 1.0real));
    }

    transition!{
        update(x: Option<Perm>) {
            remove reader -= {(None, 1.0real)};
            require x.is_some();
            add reader += {(x, 1.0real)};
            deposit storage += Some(x.unwrap());
        }
    }

    #[inductive(update)]
    fn update_inductive(pre: Self, post: Self, x: Option<Perm>) {
        let oldx = None;
        assert(sum(pre.reader) == 1.0real);
        lemma_sum_remove(pre.reader, (oldx, 1.0real));
        assert(pre.storage.is_none());
        let reader1 = pre.reader.remove((oldx, 1.0real));
        assert(sum(reader1) == 0.0real);
        lemma_sum_positive(reader1);
        lemma_sum_insert(reader1, (x, 1.0real));
    }


    transition!{
        merge(x: Option<Perm>, shares1: real, shares2: real) {
            let new_shares = shares1 + shares2;
            remove reader -= {(x, shares1)};
            remove reader -= {(x, shares2)};
            add reader += {(x, new_shares)};
        }
    }

    #[inductive(merge)]
    fn merge_inductive(pre: Self, post: Self, x: Option<Perm>, shares1: real, shares2: real) {
        let new_shares = shares1 + shares2;
        let reader1 = pre.reader.remove((x, shares1));
        let reader2 = reader1.remove((x, shares2));
        lemma_sum_remove(pre.reader, (x, shares1));
        lemma_sum_remove(reader1, (x, shares2));
        lemma_sum_insert(reader2, (x, shares1 + shares2));
        // The merged share is still within the whole, because what is left over after removing
        // both tokens cannot be negative. With `nat` shares that was free; with reals it needs
        // the positivity of every remaining share.
        assert forall|e: (Option<Perm>, real)| #[trigger]
            reader2.count(e) > 0 implies e.count() > 0.0real by {
            assert(pre.reader.count(e) > 0);
        }
        lemma_sum_positive(reader2);
    }
});

verus! {

/// A share of the ownership of a tracked `T`.
///
/// Every live token holds a positive share and the shares sum to `1`. Holding the full `1` means
/// sole ownership, which is what [`FracPerm::take`] and [`FracPerm::update`] require. Any share at
/// all is enough to [`borrow`](FracPerm::borrow) the value or to learn, via
/// [`is_same`](FracPerm::is_same), that another token sees the same value.
pub tracked struct FracPerm<T> {
    tracked inst: frac_inner::Instance<T>,
    tracked reader: frac_inner::reader<T>,
}

impl<T> FracPerm<T> {
    #[verifier::type_invariant]
    pub closed spec fn wf(self) -> bool {
        &&& self.reader.instance_id() == self.inst.id()
    }

    pub closed spec fn view(self) -> Option<T> {
        self.reader.element().0
    }

    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    pub closed spec fn shares(&self) -> real {
        self.reader.element().1
    }

    pub open spec fn valid(&self) -> bool {
        self@.is_some()
    }

    pub proof fn new(tracked v: T) -> (tracked s: Self)
        ensures
            s.valid(),
            s@ == Some(v),
            s.shares() == 1.0real,
    {
        let tracked (Tracked(inst), Tracked(mut readers)) = frac_inner::Instance::initialize_once(
            None,
        );
        let tracked reader = readers.remove((None, 1.0real));
        let tracked reader = inst.update(Some(v), v, reader);
        FracPerm { inst, reader }
    }

    pub proof fn empty() -> (tracked s: Self)
        ensures
            !s.valid(),
            s.shares() == 1.0real,
    {
        let tracked (Tracked(inst), Tracked(mut readers)) = frac_inner::Instance::initialize_once(
            None,
        );
        let tracked reader = readers.remove((None, 1.0real));
        FracPerm { inst, reader }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires
            self.valid(),
        ensures
            Some(*t) == self@,
    {
        use_type_invariant(&*self);
        self.inst.reader_guard(self.view(), self.shares(), &self.reader)
    }

    pub proof fn is_same(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        use_type_invariant(self);
        use_type_invariant(other);
        self.inst.is_same(
            (self@, self.shares()),
            (other@, other.shares()),
            &self.reader,
            &other.reader,
        );
    }

    /// Two tokens of the same instance hold shares that together are at most the whole.
    ///
    /// `other` by shared reference; `self` by `&mut` only so its token can be handed to the
    /// transition and put straight back. What comes back is a *fresh* token, so the ensures
    /// states that its id, value and share are unchanged rather than that it is the same token.
    pub proof fn two_shares_bounded(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).shares() + other.shares() <= 1.0real,
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self).shares() == old(self).shares(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        let tracked mut perm = FracPerm::empty();
        tracked_swap(self, &mut perm);
        let ghost v = perm@;
        let ghost shares = perm.shares();
        let tracked FracPerm { inst, reader } = perm;
        let tracked new_reader = inst.two_shares_bounded(
            (v, shares),
            (other@, other.shares()),
            reader,
            &other.reader,
        );
        *self = FracPerm { inst, reader: new_reader };
    }

    pub proof fn share_is_at_most_the_whole(tracked &self)
        ensures
            self.shares() <= 1.0real,
    {
        use_type_invariant(self);
        self.inst.share_is_at_most_the_whole((self@, self.shares()), &self.reader);
    }

    pub proof fn shares_positive(tracked &self)
        ensures
            self.shares() > 0.0real,
    {
        use_type_invariant(self);
        self.inst.shares_positive((self@, self.shares()), &self.reader);
    }

    pub proof fn share(tracked &mut self, n: real) -> (tracked ret: Self)
        requires
            0.0real < n < old(self).shares(),
        ensures
            ret@ == old(self)@,
            final(self)@ == old(self)@,
            final(self).id() == old(self).id(),
            ret.id() == old(self).id(),
            ret.shares() + final(self).shares() == old(self).shares(),
            ret.shares() == n,
    {
        use_type_invariant(&*self);
        let tracked mut perm = FracPerm::empty();
        tracked_swap(self, &mut perm);
        let tracked (Tracked(r1), Tracked(r2)) = perm.inst.do_share(
            perm.view(),
            perm.shares(),
            n,
            perm.reader,
        );
        *self = FracPerm { inst: perm.inst, reader: r2 };
        FracPerm { inst: perm.inst, reader: r1 }
    }

    pub proof fn merge(tracked &mut self, tracked other: Self)
        requires
            old(self)@ == other@,
            old(self).valid(),
            other.valid(),
            old(self).id() == other.id(),
        ensures
            final(self)@ == old(self)@,
            final(self).shares() == old(self).shares() + other.shares(),
            final(self).id() == old(self).id(),
            final(self).valid(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        let tracked mut perm = FracPerm::empty();
        tracked_swap(self, &mut perm);
        let shares = perm.shares();
        let tracked FracPerm { inst, reader } = perm;
        let tracked (new_reader) = inst.merge(other@, shares, other.shares(), reader, other.reader);
        *self = FracPerm { inst: inst, reader: new_reader }
    }

    pub proof fn update(tracked &mut self, tracked v: T)
        requires
            !old(self).valid(),
            old(self).shares() == 1.0real,
        ensures
            final(self).valid(),
            final(self)@ == Some(v),
            final(self).id() == old(self).id(),
            final(self).shares() == old(self).shares(),
    {
        use_type_invariant(&*self);
        let tracked mut perm = FracPerm::empty();
        tracked_swap(self, &mut perm);
        let tracked FracPerm { inst, reader } = perm;
        let tracked reader = inst.update(Some(v), v, reader);
        *self = FracPerm { inst, reader };
    }

    pub proof fn extract(tracked self) -> (tracked ret: (T, Self))
        requires
            self.valid(),
            self.shares() == 1.0real,
        ensures
            Some(ret.0) == self@,
            ret.1.id() == self.id(),
            !ret.1.valid(),
            ret.1.shares() == 1.0real,
    {
        use_type_invariant(&self);
        let tracked FracPerm { mut inst, mut reader } = self;
        let tracked (Tracked(ret), Tracked(reader)) = inst.take(reader.element().0, reader);

        (ret, FracPerm { inst, reader })
    }

    pub proof fn take(tracked &mut self) -> (tracked ret: T)
        requires
            old(self).valid(),
            old(self).shares() == 1.0real,
        ensures
            Some(ret) == old(self)@,
            final(self).id() == old(self).id(),
            !final(self).valid(),
            final(self).shares() == 1.0real,
    {
        use_type_invariant(&*self);
        let tracked mut perm = FracPerm::empty();
        tracked_swap(self, &mut perm);
        let tracked (ret, mut new) = perm.extract();
        tracked_swap(self, &mut new);
        ret
    }
}

/// A fractional ghost value, matching the API of `vstd::resource::frac::FracGhost`.
///
/// `frac()` is just the share this token holds, always between `0` and `1`. The value it carries
/// is `Ghost<T>`, i.e. pure
/// ghost data, so nothing is stored that a holder would want to borrow -- readers just look at
/// `@`. (If you need to hand out a `&T` to a real tracked value, use `FracPerm<T>` directly and
/// call `borrow`.)
///
/// `bounded_with` matches vstd's signature, taking `other` by `&`. Getting there took a detour:
/// two *borrowed* multiset tokens carrying the same element cannot be told apart from one token
/// borrowed twice, so no `property!` can bound their sum. `FracPerm::two_shares_bounded` removes
/// one of them and adds it straight back, which forces the multiset to contain both occurrences
/// while leaving the state untouched.
pub tracked struct FracGhost<T> {
    inner: FracPerm<Ghost<T>>,
}

impl<T> FracGhost<T> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.inner.valid()
    }

    pub closed spec fn id(self) -> InstanceId {
        self.inner.id()
    }

    pub closed spec fn view(self) -> T {
        self.inner@->Some_0@
    }

    pub closed spec fn frac(self) -> real {
        self.inner.shares()
    }

    pub open spec fn valid(self, id: InstanceId, frac: real) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    /// A fresh value, wholly owned.
    pub proof fn new(v: T) -> (tracked r: Self)
        ensures
            r.frac() == 1.0real,
            r@ == v,
    {
        let tracked g: Ghost<T> = Ghost(v);
        FracGhost { inner: FracPerm::new(g) }
    }

    /// A well-typed placeholder carrying no information.
    pub proof fn dummy() -> (tracked r: Self) {
        Self::new(arbitrary())
    }

    /// Two tokens of the same value always see the same thing.
    pub proof fn agree(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        use_type_invariant(self);
        use_type_invariant(other);
        self.inner.is_same(&other.inner);
    }

    pub proof fn bounded(tracked &self)
        ensures
            0.0real < self.frac() <= 1.0real,
    {
        use_type_invariant(self);
        self.inner.shares_positive();
        self.inner.share_is_at_most_the_whole();
    }

    /// Move the token out, leaving a placeholder behind.
    pub proof fn take(tracked &mut self) -> (tracked r: Self)
        ensures
            r == *old(self),
    {
        let tracked mut placeholder = Self::dummy();
        tracked_swap(self, &mut placeholder);
        placeholder
    }

    /// Peel `result_frac` off this token.
    pub proof fn split_to(tracked &mut self, result_frac: real) -> (tracked r: Self)
        requires
            0.0real < result_frac < old(self).frac(),
        ensures
            r.id() == old(self).id(),
            final(self).id() == old(self).id(),
            r@ == old(self)@,
            final(self)@ == old(self)@,
            r.frac() == result_frac,
            final(self).frac() == old(self).frac() - result_frac,
    {
        use_type_invariant(&*self);
        let tracked mut whole = Self::dummy();
        tracked_swap(self, &mut whole);
        let tracked FracGhost { mut inner } = whole;
        let tracked peeled = inner.share(result_frac);
        let tracked mut kept = FracGhost { inner };
        tracked_swap(self, &mut kept);
        FracGhost { inner: peeled }
    }

    /// Split this token in half.
    pub proof fn split(tracked &mut self) -> (tracked r: Self)
        ensures
            r.id() == old(self).id(),
            final(self).id() == old(self).id(),
            r@ == old(self)@,
            final(self)@ == old(self)@,
            r.frac() == old(self).frac() / 2.0real,
            final(self).frac() == old(self).frac() / 2.0real,
    {
        self.bounded();
        let ghost half = self.frac() / 2.0real;
        self.split_to(half)
    }

    /// Put two tokens of the same value back together.
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ == other@,
            final(self).frac() == old(self).frac() + other.frac(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        self.agree(&other);
        let tracked mut mine = Self::dummy();
        tracked_swap(self, &mut mine);
        let tracked FracGhost { mut inner } = mine;
        let tracked FracGhost { inner: theirs } = other;
        inner.merge(theirs);
        let tracked mut joined = FracGhost { inner };
        tracked_swap(self, &mut joined);
    }

    /// Change the value. Only the sole owner may do this.
    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).frac() == 1.0real,
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self)@ == v,
    {
        use_type_invariant(&*self);
        let tracked mut mine = Self::dummy();
        tracked_swap(self, &mut mine);
        let tracked FracGhost { mut inner } = mine;
        let tracked _discarded = inner.take();
        let tracked g: Ghost<T> = Ghost(v);
        inner.update(g);
        let tracked mut updated = FracGhost { inner };
        tracked_swap(self, &mut updated);
    }

    /// Change the value, given two tokens that together make up the whole.
    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == 1.0real,
        ensures
            final(self).id() == old(self).id(),
            final(other).id() == old(other).id(),
            final(self).frac() == old(self).frac(),
            final(other).frac() == old(other).frac(),
            final(self)@ == v,
            final(other)@ == v,
    {
        self.bounded();
        other.bounded();
        let ghost other_frac = other.frac();
        let tracked theirs = other.take();
        self.combine(theirs);
        self.update(v);
        let tracked mut back = self.split_to(other_frac);
        tracked_swap(other, &mut back);
    }

    /// Matching vstd's `bounded_with`: `other` by shared reference.
    ///
    /// `self` is `&mut` only so its token can be lent to the state machine and put straight back.
    /// vstd additionally ensures `*old(self) == *final(self)`; here the token handed back is a
    /// fresh one, so only its id, value and share are promised unchanged.
    pub proof fn bounded_with(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            0.0real < old(self).frac() + other.frac() <= 1.0real,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self)@ == old(self)@,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.bounded();
        other.bounded();
        self.inner.two_shares_bounded(&other.inner);
    }
}

impl<T> FracPerm<vstd::raw_ptr::PointsTo<T>> {
    pub open spec fn addr(&self) -> int
        recommends
            self.valid(),
    {
        self@.unwrap().ptr()@.addr as int
    }
}

} // verus!
  // Proof helpers for the multiset of fractional shares.
verus! {

/// Something that holds a share.
pub trait CountTrait {
    spec fn count(&self) -> real;
}

/// The total share held across a multiset of tokens.
pub open spec fn sum<T: CountTrait>(s: Multiset<T>) -> real
    decreases s.len(),
{
    if s.len() > 0 {
        let e = s.choose();
        e.count() + sum(s.remove(e))
    } else {
        0.0real
    }
}

pub proof fn lemma_sum_insert<T: CountTrait>(s: Multiset<T>, elem: T)
    ensures
        sum(s) + elem.count() == sum(s.insert(elem)),
{
    assert(s.insert(elem).remove(elem) =~= s);
    lemma_sum_remove(s.insert(elem), elem);
}

pub proof fn lemma_sum_remove<T: CountTrait>(s: Multiset<T>, elem: T)
    requires
        s.contains(elem),
    ensures
        sum(s.remove(elem)) + elem.count() == sum(s),
    decreases s.len(),
{
    let news = s.remove(elem);
    if s.len() > 1 {
        let e = s.choose();
        if e != elem {
            assert(sum(s.remove(e)) + e.count() == sum(s));
            lemma_sum_remove(s.remove(e), elem);
            lemma_sum_remove(s.remove(elem), e);
            assert(s.remove(elem).remove(e) =~= s.remove(e).remove(elem));
        } else {
            assert(sum(s.remove(elem)) + elem.count() == sum(s));
        }
    } else {
        Multiset::lemma_is_singleton(s);
        let e = s.choose();
        assert(s.contains(e));
        assert(news.len() == 0);
        assert(sum(news) == 0.0real);
        assert(e == elem);
    }
}

/// If every token holds a positive share, the total is positive too -- and in particular, a total
/// of zero means there are no tokens left.
///
/// With `nat` shares this would be free. With `real` shares it has to be proved, and it is the
/// only place the switch to reals costs anything.
pub proof fn lemma_sum_positive<T: CountTrait>(s: Multiset<T>)
    requires
        forall|e: T| #[trigger] s.count(e) > 0 ==> e.count() > 0.0real,
    ensures
        sum(s) >= 0.0real,
        s.len() > 0 ==> sum(s) > 0.0real,
    decreases s.len(),
{
    if s.len() > 0 {
        let e = s.choose();
        vstd::multiset::axiom_choose_count(s);
        assert(s.count(e) > 0);
        let rest = s.remove(e);
        assert forall|x: T| #[trigger] rest.count(x) > 0 implies x.count() > 0.0real by {
            assert(s.count(x) > 0);
        }
        lemma_sum_positive(rest);
    }
}

impl<T> CountTrait for (T, real) {
    open spec fn count(&self) -> real {
        self.1
    }
}

} // verus!

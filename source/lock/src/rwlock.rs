//! A reader/writer lock that spins on one atomic counter.
//!
//! The counter says how many readers hold the lock, except for one value --
//! `usize::MAX` -- which says a writer holds it. So a writer takes the lock by
//! exchanging `0` for that value, which succeeds only when there is no reader
//! and no other writer, and a reader takes it by exchanging `n` for `n + 1`,
//! which succeeds only when the value it read was a reader count and has not
//! changed since.
//!
//! What the counter cannot say by itself is who is allowed to touch the
//! contents. That is the state machine below: the contents live in its
//! storage, a writer *withdraws* them and must deposit them back, and a reader
//! gets a token that *guards* the storage -- proof that the contents are there
//! and unchanging for as long as the token is held. The counter and the state
//! machine are kept in step by the atomic's invariant, so a successful
//! exchange is exactly the moment a transition is allowed.
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::multiset::Multiset;
use vstd::pervasive::proof_from_false;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use crate::pred::LockPredicate;
use crate::spin::CellInv;

verus! {

/// The counter value that means "a writer holds the lock".
///
/// Taken out of the reader range, so a lock can hold `usize::MAX - 1` readers
/// at once and refuses the one that would overflow into this value.
pub open spec fn spec_write_state() -> nat {
    usize::MAX as nat
}

} // verus!

tokenized_state_machine!(
RwToks<V, Pred: LockPredicate<V>> {
    fields {
        #[sharding(constant)]
        pub pred: Pred,

        /// Mirrors the atomic counter.
        #[sharding(variable)]
        pub state: nat,

        /// The contents, when nobody is writing them.
        #[sharding(storage_option)]
        pub storage: Option<V>,

        /// Held by the one writer, if there is one.
        #[sharding(option)]
        pub writer: Option<()>,

        /// One per reader, each naming the contents it is reading.
        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }

    init!{
        initialize(pred: Pred, v: V) {
            require pred.inv(v);
            init pred = pred;
            init state = 0;
            init storage = Option::Some(v);
            init writer = Option::None;
            init reader = Multiset::empty();
        }
    }

    /// Take the lock for writing, which is possible only from `0`: no reader
    /// holds it and no writer does.
    transition!{
        acquire_write() {
            require(pre.state == 0);
            update state = spec_write_state();
            add writer += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert pre.pred.inv(x);
        }
    }

    /// Give the contents back. They have to satisfy the predicate again,
    /// because the next reader is entitled to assume it.
    transition!{
        release_write(x: V) {
            require pre.pred.inv(x);
            remove writer -= Some(());
            update state = 0;
            deposit storage += Some(x);
        }
    }

    /// Take the lock for reading. Any counter value below the writer's is a
    /// reader count, and one short of it is where the count stops.
    transition!{
        acquire_read() {
            require(pre.state + 1 < spec_write_state());
            update state = (pre.state + 1) as nat;

            birds_eye let x = pre.storage->0;
            add reader += {x};

            assert pre.pred.inv(x);
        }
    }

    transition!{
        release_read(x: V) {
            remove reader -= {x};
            assert(pre.state >= 1 && pre.state < spec_write_state()) by {
                broadcast use vstd::multiset::group_multiset_axioms;

                assert(pre.reader.count(x) > 0);
                assert(pre.storage == Option::Some(x));
                assert(pre.writer is None);
                assert(pre.state == pre.reader.count(pre.storage->0));
            };
            update state = (pre.state - 1) as nat;
        }
    }

    /// A reader's token is proof that the contents are there and are `x`.
    property!{
        read_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    /// Whether a writer holds the lock is the one thing the counter says
    /// exactly, and the contents are out of storage exactly then.
    #[invariant]
    pub fn writer_matches(&self) -> bool {
        &&& (self.writer is Some <==> self.storage is None)
        &&& (self.writer is Some <==> self.state == spec_write_state())
    }

    /// Every reader is reading the same thing, which is what is in storage.
    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall|t: V| #[trigger] self.reader.count(t) > 0 ==> self.storage == Option::Some(t)
    }

    /// When the counter is a count, it is the number of readers.
    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.state != spec_write_state() ==> self.state == self.reader.count(self.storage->0)
    }

    /// The counter never leaves the range a `usize` can hold.
    #[invariant]
    pub fn state_bounded(&self) -> bool {
        self.state <= spec_write_state()
    }

    #[invariant]
    pub fn storage_inv(&self) -> bool {
        self.storage is Some ==> self.pred.inv(self.storage->0)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, pred: Pred, v: V) {
        broadcast use vstd::multiset::group_multiset_axioms;
    }

    #[inductive(acquire_write)]
    fn acquire_write_inductive(pre: Self, post: Self) {
        broadcast use vstd::multiset::group_multiset_axioms;
        assert forall|t: V| post.reader.count(t) == 0 by {
            if post.reader.count(t) > 0 {
                assert(pre.storage == Option::Some(t));
            }
        }
    }

    #[inductive(release_write)]
    fn release_write_inductive(pre: Self, post: Self, x: V) {
        broadcast use vstd::multiset::group_multiset_axioms;
        assert forall|t: V| post.reader.count(t) == 0 by {
            if post.reader.count(t) > 0 {
                assert(pre.storage == Option::Some(t));
            }
        }
    }

    #[inductive(acquire_read)]
    fn acquire_read_inductive(pre: Self, post: Self) {
        broadcast use vstd::multiset::group_multiset_axioms;
    }

    #[inductive(release_read)]
    fn release_read_inductive(pre: Self, post: Self, x: V) {
        broadcast use vstd::multiset::group_multiset_axioms;
        assert(pre.storage == Option::Some(x));
    }
});

verus! {

/// The counter and the state machine's mirror of it are the same number.
pub struct RwInv<V, Pred> {
    dummy: PhantomData<(V, Pred)>,
}

impl<V, Pred: LockPredicate<V>> AtomicInvariantPredicate<
    InstanceId,
    usize,
    RwToks::state<V, Pred>,
> for RwInv<V, Pred> {
    open spec fn atomic_inv(k: InstanceId, u: usize, g: RwToks::state<V, Pred>) -> bool {
        &&& g.instance_id() == k
        &&& g.value() == u as nat
    }
}

/// The counter value that means "a writer holds the lock".
pub const WRITE_STATE: usize = usize::MAX;

/// A reader/writer lock over tracked state.
///
/// Guards nothing the compiler can see; [`RwLock`] is this lock over a cell,
/// for the ordinary case of a lock that owns its data.
pub struct RawRwLock<V, Pred: LockPredicate<V>> {
    state: AtomicUsize<InstanceId, RwToks::state<V, Pred>, RwInv<V, Pred>>,
    inst: Tracked<RwToks::Instance<V, Pred>>,
    pred: Ghost<Pred>,
}

impl<V, Pred: LockPredicate<V>> RawRwLock<V, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.state.well_formed()
        &&& self.state.constant() == self.inst@.id()
        &&& self.inst@.pred() == self.pred@
    }

    /// The predicate this lock's contents satisfy.
    pub closed spec fn pred(&self) -> Pred {
        self.pred@
    }

    /// What is true of the contents whenever no one is writing them.
    pub open spec fn inv(&self, v: V) -> bool {
        self.pred().inv(v)
    }

    /// Which lock a token belongs to.
    pub closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    /// Builds a lock, free, holding `v`.
    pub fn new(Tracked(v): Tracked<V>, Ghost(pred): Ghost<Pred>) -> (ret: Self)
        requires
            pred.inv(v),
        ensures
            ret.pred() == pred,
    {
        let tracked (Tracked(inst), Tracked(state_tok), _, _) = RwToks::Instance::initialize(
            pred,
            v,
            Some(v),
        );
        let state = AtomicUsize::new(Ghost(inst.id()), 0, Tracked(state_tok));
        RawRwLock { state, inst: Tracked(inst), pred: Ghost(pred) }
    }

    /// Takes the lock for writing if it is free right now, and does not spin.
    pub fn try_write(&self) -> (ret: Option<(Tracked<V>, WriteToken<V, Pred>)>)
        ensures
            ret matches Some((v, token)) ==> self.inv(v@) && token.lock_id() == self.id(),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked mut got: Option<V> = None;
        let tracked mut handle: Option<RwToks::writer<V, Pred>> = None;
        let res =
            atomic_with_ghost!(
            &self.state => compare_exchange(0, WRITE_STATE);
            returning res;
            ghost g =>
        {
            if res is Ok {
                let tracked (_, Tracked(v), Tracked(w)) = self.inst.borrow().acquire_write(&mut g);
                got = Some(v);
                handle = Some(w);
            }
        });
        match res {
            Ok(_) => {
                let tracked v = match got {
                    Some(v) => v,
                    None => proof_from_false(),
                };
                let tracked w = match handle {
                    Some(w) => w,
                    None => proof_from_false(),
                };
                Some((Tracked(v), WriteToken { handle: Tracked(w) }))
            },
            Err(_) => None,
        }
    }

    /// Takes the lock for writing, spinning until it is free.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_write(&self) -> (ret: (Tracked<V>, WriteToken<V, Pred>))
        ensures
            self.inv(ret.0@),
            ret.1.lock_id() == self.id(),
    {
        loop {
            match self.try_write() {
                Some(got) => {
                    return got;
                },
                None => {},
            }
        }
    }

    /// Gives the contents back and frees the lock.
    pub fn release_write(&self, Tracked(v): Tracked<V>, token: WriteToken<V, Pred>)
        requires
            self.inv(v),
            token.lock_id() == self.id(),
    {
        proof {
            use_type_invariant(self);
        }
        let WriteToken { handle: Tracked(handle) } = token;
        atomic_with_ghost!(
            &self.state => store(0);
            ghost g =>
        {
            self.inst.borrow().release_write(v, &mut g, v, handle);
        });
    }

    /// Takes the lock for reading if no writer holds it right now, and does
    /// not spin.
    pub fn try_read(&self) -> (ret: Option<ReadToken<V, Pred>>)
        ensures
            ret matches Some(token) ==> token.lock_id() == self.id() && self.inv(token.value()),
    {
        proof {
            use_type_invariant(self);
        }
        let cur = self.state.load();
        if cur >= WRITE_STATE - 1 {
            return None;
        }
        let tracked mut handle: Option<RwToks::reader<V, Pred>> = None;
        let res =
            atomic_with_ghost!(
            &self.state => compare_exchange(cur, cur + 1);
            returning res;
            ghost g =>
        {
            if res is Ok {
                let tracked (_, Tracked(r)) = self.inst.borrow().acquire_read(&mut g);
                handle = Some(r);
            }
        });
        match res {
            Ok(_) => {
                let tracked r = match handle {
                    Some(r) => r,
                    None => proof_from_false(),
                };
                Some(ReadToken { handle: Tracked(r) })
            },
            Err(_) => None,
        }
    }

    /// Takes the lock for reading, spinning until no writer holds it.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_read(&self) -> (ret: ReadToken<V, Pred>)
        ensures
            ret.lock_id() == self.id(),
            self.inv(ret.value()),
    {
        loop {
            match self.try_read() {
                Some(token) => {
                    return token;
                },
                None => {},
            }
        }
    }

    /// The contents, for as long as the reader's token is held.
    pub fn borrow_read<'a>(&'a self, token: &'a ReadToken<V, Pred>) -> (ret: Tracked<&'a V>)
        requires
            token.lock_id() == self.id(),
        ensures
            *ret@ == token.value(),
    {
        proof {
            use_type_invariant(self);
        }
        let tracked v = self.inst.borrow().read_guard(token.value(), token.handle.borrow());
        Tracked(v)
    }

    /// Stops reading.
    pub fn release_read(&self, token: ReadToken<V, Pred>)
        requires
            token.lock_id() == self.id(),
    {
        proof {
            use_type_invariant(self);
        }
        let ghost x = token.value();
        let ReadToken { handle: Tracked(handle) } = token;
        atomic_with_ghost!(
            &self.state => fetch_sub(1);
            ghost g =>
        {
            self.inst.borrow().release_read(x, &mut g, handle);
        });
    }
}

/// Proof that the write lock is held. Give it back to
/// [`RawRwLock::release_write`].
pub struct WriteToken<V, Pred: LockPredicate<V>> {
    handle: Tracked<RwToks::writer<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> WriteToken<V, Pred> {
    /// The lock this token was taken from.
    pub closed spec fn lock_id(&self) -> InstanceId {
        self.handle@.instance_id()
    }
}

/// Proof that a read lock is held, and what is being read.
pub struct ReadToken<V, Pred: LockPredicate<V>> {
    handle: Tracked<RwToks::reader<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> ReadToken<V, Pred> {
    /// The lock this token was taken from.
    pub closed spec fn lock_id(&self) -> InstanceId {
        self.handle@.instance_id()
    }

    /// What this reader is reading. It cannot change while the token is held.
    pub closed spec fn value(&self) -> V {
        self.handle@.element()
    }
}

/// A reader/writer lock that owns its data, in the shape of
/// `std::sync::RwLock`.
///
/// Unlike `std::sync::RwLock`, dropping a guard does *not* release the lock --
/// [`WriteGuard::unlock`] and [`ReadGuard::unlock`] do, and Verus does not
/// check that they are called.
pub struct RwLock<T, Pred: LockPredicate<T>> {
    cell: PCell<T>,
    raw: RawRwLock<PointsTo<T>, CellInv<Pred>>,
}

impl<T, Pred: LockPredicate<T>> RwLock<T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.raw.pred().cell == self.cell.id()
    }

    /// What is true of the data whenever no one is writing it.
    pub closed spec fn inv(&self, v: T) -> bool {
        self.raw.pred().pred.inv(v)
    }

    /// Builds a lock owning `v`.
    pub fn new(v: T, Ghost(pred): Ghost<Pred>) -> (ret: Self)
        requires
            pred.inv(v),
        ensures
            forall|w: T| ret.inv(w) == pred.inv(w),
    {
        let (cell, Tracked(perm)) = PCell::new(v);
        let ghost cell_pred = CellInv { cell: cell.id(), pred };
        let raw = RawRwLock::new(Tracked(perm), Ghost(cell_pred));
        RwLock { cell, raw }
    }

    /// Takes the lock for writing, spinning until it is free.
    pub fn write(&self) -> (ret: WriteGuard<'_, T, Pred>)
        ensures
            ret.lock() == self,
    {
        proof {
            use_type_invariant(self);
        }
        let (Tracked(perm), token) = self.raw.acquire_write();
        WriteGuard { lock: self, perm: Tracked(perm), token }
    }

    /// Takes the lock for reading, spinning until no writer holds it.
    pub fn read(&self) -> (ret: ReadGuard<'_, T, Pred>)
        ensures
            ret.lock() == self,
    {
        proof {
            use_type_invariant(self);
        }
        let token = self.raw.acquire_read();
        ReadGuard { lock: self, token }
    }

    /// Dissolves the lock and returns the data, spinning until it is free.
    pub fn into_inner(self) -> (ret: T)
        ensures
            self.inv(ret),
    {
        proof {
            use_type_invariant(&self);
        }
        let RwLock { cell, raw } = self;
        let (Tracked(perm), _token) = raw.acquire_write();
        cell.into_inner(Tracked(perm))
    }
}

/// Proof that the write lock is held, and the way to the data while it is.
pub struct WriteGuard<'a, T, Pred: LockPredicate<T>> {
    lock: &'a RwLock<T, Pred>,
    perm: Tracked<PointsTo<T>>,
    token: WriteToken<PointsTo<T>, CellInv<Pred>>,
}

impl<'a, T, Pred: LockPredicate<T>> WriteGuard<'a, T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@.id() == self.lock.cell.id()
        &&& self.token.lock_id() == self.lock.raw.id()
    }

    /// The lock this guard was taken from.
    pub closed spec fn lock(&self) -> &RwLock<T, Pred> {
        self.lock
    }

    /// The data as it stands.
    pub closed spec fn view(&self) -> T {
        *self.perm@.value()
    }

    /// Releases the lock. The data has to satisfy the lock's predicate again.
    pub fn unlock(self)
        requires
            self.lock().inv(self@),
    {
        proof {
            use_type_invariant(&self);
        }
        let WriteGuard { lock, perm: Tracked(perm), token } = self;
        lock.raw.release_write(Tracked(perm), token);
    }
}

impl<'a, T, Pred: LockPredicate<T>> Deref for WriteGuard<'a, T, Pred> {
    type Target = T;

    fn deref(&self) -> (ret: &T)
        ensures
            *ret == self@,
    {
        proof {
            use_type_invariant(self);
        }
        self.lock.cell.borrow(Tracked(self.perm.borrow()))
    }
}

impl<'a, T, Pred: LockPredicate<T>> DerefMut for WriteGuard<'a, T, Pred> {
    fn deref_mut(&mut self) -> (ret: &mut T)
        ensures
            *ret == old(self)@,
            final(self)@ == *final(ret),
            final(self).lock() == old(self).lock(),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.lock.cell.borrow_mut(Tracked(self.perm.borrow_mut()))
    }
}

/// Proof that a read lock is held, and the way to the data while it is.
pub struct ReadGuard<'a, T, Pred: LockPredicate<T>> {
    lock: &'a RwLock<T, Pred>,
    token: ReadToken<PointsTo<T>, CellInv<Pred>>,
}

impl<'a, T, Pred: LockPredicate<T>> ReadGuard<'a, T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.token.lock_id() == self.lock.raw.id()
        &&& self.token.value().id() == self.lock.cell.id()
    }

    /// The lock this guard was taken from.
    pub closed spec fn lock(&self) -> &RwLock<T, Pred> {
        self.lock
    }

    /// The data, which no writer can change while this guard is held.
    pub closed spec fn view(&self) -> T {
        *self.token.value().value()
    }

    /// Stops reading.
    pub fn unlock(self) {
        proof {
            use_type_invariant(&self);
        }
        let ReadGuard { lock, token } = self;
        lock.raw.release_read(token);
    }
}

impl<'a, T, Pred: LockPredicate<T>> Deref for ReadGuard<'a, T, Pred> {
    type Target = T;

    fn deref(&self) -> (ret: &T)
        ensures
            *ret == self@,
    {
        proof {
            use_type_invariant(self);
        }
        let Tracked(perm) = self.lock.raw.borrow_read(&self.token);
        self.lock.cell.borrow(Tracked(perm))
    }
}

} // verus!

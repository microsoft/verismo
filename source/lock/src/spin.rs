//! A fair spin lock: threads are served in the order they arrived.
//!
//! Two counters. `current` is the next ticket to hand out, `holder` is the
//! ticket being served. A thread takes a ticket by bumping `current`, then
//! spins on plain loads of `holder` until its number comes up; releasing bumps
//! `holder`, which serves whoever is next. Nobody overtakes anybody, so no
//! thread starves while others keep grabbing the lock.
//!
//! Behind the counters sits the thing the lock guards, held as ghost state.
//! The invariant is that the ghost slot is full exactly when nobody is being
//! served, so reaching the head of the queue is what takes the contents out
//! and bumping `holder` is what puts them back. Only one thread can be at the
//! head of the queue at a time, and only the thread at the head owns the
//! token that lets `holder` move, so there can be at most one holder and a
//! thread that is not holding the lock cannot release it.
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::cell::CellId;
use vstd::pervasive::proof_from_false;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use crate::pred::LockPredicate;

verus! {

/// The last ticket that can be issued, past which the counter would wrap.
pub open spec fn spec_max_ticket() -> nat {
    u64::MAX as nat
}

} // verus!
// Who is queued, who is being served, and where the contents are.
tokenized_state_machine! {
TicketToks<V, Pred: LockPredicate<V>> {
    fields {
        #[sharding(constant)]
        pub pred: Pred,

        /// The next ticket to hand out.
        #[sharding(variable)]
        pub current: nat,

        /// The ticket being served.
        #[sharding(variable)]
        pub holder: nat,

        /// One token per thread that has taken a ticket and is still waiting.
        #[sharding(map)]
        pub tickets: Map<nat, ()>,

        /// The ticket of the thread that has reached the head of the queue.
        #[sharding(option)]
        pub holding: Option<nat>,

        /// The contents, here whenever nobody is being served.
        #[sharding(storage_option)]
        pub storage: Option<V>,
    }

    #[invariant]
    pub fn queue_ordered(&self) -> bool {
        self.holder <= self.current
    }

    #[invariant]
    pub fn holder_bounded(&self) -> bool {
        self.holder <= spec_max_ticket()
    }

    /// The counters are `u64`s in the running code, so `current` has to stay
    /// where one fits.
    #[invariant]
    pub fn current_bounded(&self) -> bool {
        self.current <= spec_max_ticket()
    }

    #[invariant]
    pub fn tickets_waiting(&self) -> bool {
        forall|k: nat| #[trigger]
            self.tickets.dom().contains(k) ==> self.holder <= k && k < self.current
    }

    #[invariant]
    pub fn holder_is_served(&self) -> bool {
        self.holding is Some ==> {
            &&& self.holding->0 == self.holder
            &&& self.holder < self.current
            &&& !self.tickets.dom().contains(self.holder)
        }
    }

    #[invariant]
    pub fn contents_when_unserved(&self) -> bool {
        &&& (self.storage is Some) == (self.holding is None)
        &&& self.storage is Some ==> self.pred.inv(self.storage->0)
    }

    init!{
        initialize(pred: Pred, v: V) {
            require pred.inv(v);
            init pred = pred;
            init current = 0;
            init holder = 0;
            init tickets = Map::empty();
            init holding = Option::None;
            init storage = Option::Some(v);
        }
    }

    transition!{
        take_ticket() {
            require pre.current < spec_max_ticket();
            update current = (pre.current + 1) as nat;
            add tickets += [ pre.current => () ] by {
                assert(!pre.tickets.dom().contains(pre.current));
            };
        }
    }

    transition!{
        enter(n: nat) {
            require pre.holder == n;
            remove tickets -= [ n => () ];
            add holding += Some(n);
            birds_eye let v = pre.storage->0;
            withdraw storage -= Some(v) by {
                assert(pre.holding is None);
            };
            assert pre.pred.inv(v) by {
                assert(pre.holding is None);
            };
        }
    }

    transition!{
        leave(n: nat, v: V) {
            require pre.pred.inv(v);
            remove holding -= Some(n);
            assert pre.holder == n;
            assert pre.holder < spec_max_ticket();
            update holder = (n + 1) as nat;
            deposit storage += Some(v);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, pred: Pred, v: V) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(Map::<nat, ()>::empty().dom() =~= Set::<nat>::empty());
        }
    }

    #[inductive(take_ticket)]
    fn take_ticket_inductive(pre: Self, post: Self) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            if k != pre.current {
                assert(pre.tickets.dom().contains(k));
            }
        }
    }

    #[inductive(enter)]
    fn enter_inductive(pre: Self, post: Self, n: nat) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(pre.tickets.dom().contains(k));
        }
    }

    #[inductive(leave)]
    fn leave_inductive(pre: Self, post: Self, n: nat, v: V) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(pre.tickets.dom().contains(k));
            assert(k != pre.holder);
        }
    }
}
}

verus! {

/// What the `current` counter and its ghost token must jointly satisfy.
pub struct CurrentInv<V, Pred> {
    dummy: PhantomData<(V, Pred)>,
}

impl<V, Pred: LockPredicate<V>> AtomicInvariantPredicate<
    InstanceId,
    u64,
    TicketToks::current<V, Pred>,
> for CurrentInv<V, Pred> {
    open spec fn atomic_inv(k: InstanceId, u: u64, g: TicketToks::current<V, Pred>) -> bool {
        &&& g.instance_id() == k
        &&& g.value() == u as nat
    }
}

/// What the `holder` counter and its ghost token must jointly satisfy.
pub struct HolderInv<V, Pred> {
    dummy: PhantomData<(V, Pred)>,
}

impl<V, Pred: LockPredicate<V>> AtomicInvariantPredicate<
    InstanceId,
    u64,
    TicketToks::holder<V, Pred>,
> for HolderInv<V, Pred> {
    open spec fn atomic_inv(k: InstanceId, u: u64, g: TicketToks::holder<V, Pred>) -> bool {
        &&& g.instance_id() == k
        &&& g.value() == u as nat
    }
}

/// A place in a lock's queue.
///
/// Handed out by [`RawSpinLock::take_ticket`] and given up by entering the
/// lock. A ticket cannot be dropped back into the queue: once a thread has
/// one, the threads behind it wait until it takes the lock and releases it.
pub struct Ticket<V, Pred: LockPredicate<V>> {
    num: u64,
    tok: Tracked<TicketToks::tickets<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> Ticket<V, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.tok@.key() == self.num as nat
    }

    /// The lock this ticket queues for.
    pub closed spec fn instance_id(&self) -> InstanceId {
        self.tok@.instance_id()
    }
}

/// Proof that the caller is the one being served, and the right to serve the
/// next thread by releasing.
pub struct Hold<V, Pred: LockPredicate<V>> {
    tok: Tracked<TicketToks::holding<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> Hold<V, Pred> {
    /// The lock being held.
    pub closed spec fn instance_id(&self) -> InstanceId {
        self.tok@.instance_id()
    }
}

/// A fair spin lock over tracked state.
///
/// Guards nothing the compiler can see: what goes in and comes out is ghost,
/// which is what a lock over memory owned elsewhere -- a page's write tokens,
/// a permission to a device register -- needs. [`SpinLock`] is this lock over
/// a cell, for the ordinary case of a lock that owns its data.
///
/// There is no `try_lock`. Taking a ticket commits a thread to the queue, and
/// a thread that gave up its place would leave everyone behind it waiting for
/// a ticket that never gets served.
pub struct RawSpinLock<V, Pred: LockPredicate<V>> {
    current: AtomicU64<InstanceId, TicketToks::current<V, Pred>, CurrentInv<V, Pred>>,
    holder: AtomicU64<InstanceId, TicketToks::holder<V, Pred>, HolderInv<V, Pred>>,
    inst: Tracked<TicketToks::Instance<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> RawSpinLock<V, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.current.well_formed()
        &&& self.holder.well_formed()
        &&& self.current.constant() == self.inst@.id()
        &&& self.holder.constant() == self.inst@.id()
    }

    /// Which lock this is, for matching tickets and holds against it.
    pub closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    /// The predicate this lock's contents satisfy.
    pub closed spec fn pred(&self) -> Pred {
        self.inst@.pred()
    }

    /// What is true of the contents whenever no one holds them.
    pub open spec fn inv(&self, v: V) -> bool {
        self.pred().inv(v)
    }

    /// Builds a lock, free, holding `v`.
    pub fn new(Tracked(v): Tracked<V>, Ghost(pred): Ghost<Pred>) -> (ret: Self)
        requires
            pred.inv(v),
        ensures
            ret.pred() == pred,
    {
        let tracked (Tracked(inst), Tracked(cur_tok), Tracked(holder_tok), _, _) =
            TicketToks::Instance::initialize(pred, v, Some(v));
        let ghost id = inst.id();
        RawSpinLock {
            current: AtomicU64::new(Ghost(id), 0, Tracked(cur_tok)),
            holder: AtomicU64::new(Ghost(id), 0, Tracked(holder_tok)),
            inst: Tracked(inst),
        }
    }

    /// Joins the queue, if a ticket can be had without contention.
    ///
    /// Fails when another thread took a ticket at the same moment, or -- after
    /// `u64::MAX` acquisitions -- when the queue has run out of numbers.
    pub fn try_take_ticket(&self) -> (ret: Option<Ticket<V, Pred>>)
        ensures
            ret matches Some(t) ==> t.instance_id() == self.id(),
    {
        proof {
            use_type_invariant(self);
        }
        let cur = atomic_with_ghost!(&self.current => load(); ghost g => { });
        if cur == u64::MAX {
            return None;
        }
        let tracked mut got: Option<TicketToks::tickets<V, Pred>> = None;
        let res =
            atomic_with_ghost!(
            &self.current => compare_exchange(cur, cur + 1);
            returning res;
            ghost g =>
        {
            if res is Ok {
                got = Some(self.inst.borrow().take_ticket(&mut g));
            }
        });
        match res {
            Ok(_) => {
                let tracked tok = match got {
                    Some(tok) => tok,
                    None => proof_from_false(),
                };
                Some(Ticket { num: cur, tok: Tracked(tok) })
            },
            Err(_) => None,
        }
    }

    /// Takes the lock if this ticket is the one being served, and hands the
    /// ticket back otherwise so the caller can ask again.
    pub fn try_enter(&self, ticket: Ticket<V, Pred>) -> (ret: Result<
        (Tracked<V>, Hold<V, Pred>),
        Ticket<V, Pred>,
    >)
        requires
            ticket.instance_id() == self.id(),
        ensures
            ret matches Ok((v, hold)) ==> self.inv(v@) && hold.instance_id() == self.id(),
            ret matches Err(t) ==> t.instance_id() == self.id(),
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(&ticket);
        }
        let Ticket { num, tok: Tracked(tok) } = ticket;
        let tracked mut waiting: Option<TicketToks::tickets<V, Pred>> = Some(tok);
        let tracked mut entered: Option<V> = None;
        let tracked mut hold: Option<TicketToks::holding<V, Pred>> = None;
        let served =
            atomic_with_ghost!(
            &self.holder => load();
            returning served;
            ghost g =>
        {
            if served == num {
                let tracked t = waiting.tracked_take();
                let tracked (Tracked(h), _, Tracked(v)) = self.inst.borrow().enter(
                    num as nat,
                    &g,
                    t,
                );
                entered = Some(v);
                hold = Some(h);
            }
        });
        if served == num {
            let tracked v = match entered {
                Some(v) => v,
                None => proof_from_false(),
            };
            let tracked h = match hold {
                Some(h) => h,
                None => proof_from_false(),
            };
            Ok((Tracked(v), Hold { tok: Tracked(h) }))
        } else {
            let tracked t = match waiting {
                Some(t) => t,
                None => proof_from_false(),
            };
            Err(Ticket { num, tok: Tracked(t) })
        }
    }

    /// Takes the lock, waiting for every thread already in the queue.
    ///
    /// Nothing here bounds how long that is: a holder that never releases
    /// blocks the whole queue for ever, and this crate proves nothing about
    /// whether a waiting thread ever runs. This is one of the two functions in
    /// the crate that Verus accepts without a termination argument.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire(&self) -> (ret: (Tracked<V>, Hold<V, Pred>))
        ensures
            self.inv(ret.0@),
            ret.1.instance_id() == self.id(),
    {
        let mut ticket: Option<Ticket<V, Pred>> = None;
        loop
            invariant
                ticket matches Some(t) ==> t.instance_id() == self.id(),
        {
            let held = ticket;
            ticket = None;
            match held {
                None => {
                    ticket = self.try_take_ticket();
                },
                Some(t) => {
                    match self.try_enter(t) {
                        Ok(held) => {
                            return held;
                        },
                        Err(t) => {
                            ticket = Some(t);
                        },
                    }
                },
            }
        }
    }

    /// Gives the contents back and serves the next thread in the queue.
    ///
    /// Takes the contents rather than trusting the caller to have left them
    /// alone, so whatever is put back has to satisfy the lock's predicate.
    pub fn release(&self, hold: Hold<V, Pred>, Tracked(v): Tracked<V>)
        requires
            hold.instance_id() == self.id(),
            self.inv(v),
    {
        proof {
            use_type_invariant(self);
        }
        let Hold { tok: Tracked(tok) } = hold;
        let tracked mut held: Option<TicketToks::holding<V, Pred>> = Some(tok);
        let _ =
            atomic_with_ghost!(
            &self.holder => fetch_add(1);
            ghost g =>
        {
            let tracked t = held.tracked_take();
            let ghost n = t.value();
            self.inst.borrow().leave(n, v, &mut g, t, v);
        });
    }

    /// Dissolves the lock and returns its contents.
    ///
    /// Queues first: a lock can be consumed while another thread holds it only
    /// if that thread is done, and waiting is the only way to know.
    pub fn into_inner(self) -> (ret: Tracked<V>)
        ensures
            self.inv(ret@),
    {
        let (v, _hold) = self.acquire();
        v
    }
}

/// The predicate a [`SpinLock`]'s cell permission satisfies: it is that cell's
/// permission, and the value in the cell is what the user asked for.
pub struct CellInv<Pred> {
    pub cell: CellId,
    pub pred: Pred,
}

impl<T, Pred: LockPredicate<T>> LockPredicate<PointsTo<T>> for CellInv<Pred> {
    open spec fn inv(self, perm: PointsTo<T>) -> bool {
        &&& perm.id() == self.cell
        &&& self.pred.inv(*perm.value())
    }
}

/// A fair mutual-exclusion lock that owns its data, in the shape of
/// `std::sync::Mutex`.
///
/// [`lock`](Self::lock) hands back a guard that derefs to the data. Unlike
/// `std::sync::Mutex`, dropping the guard does *not* release the lock --
/// [`SpinGuard::unlock`] does, and Verus does not check that it is called.
pub struct SpinLock<T, Pred: LockPredicate<T>> {
    cell: PCell<T>,
    raw: RawSpinLock<PointsTo<T>, CellInv<Pred>>,
}

impl<T, Pred: LockPredicate<T>> SpinLock<T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        self.raw.pred().cell == self.cell.id()
    }

    /// What is true of the data whenever no one holds the lock.
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
        let raw = RawSpinLock::new(Tracked(perm), Ghost(cell_pred));
        SpinLock { cell, raw }
    }

    /// Takes the lock, waiting for every thread already in the queue.
    pub fn lock(&self) -> (ret: SpinGuard<'_, T, Pred>)
        ensures
            ret.lock() == self,
    {
        proof {
            use_type_invariant(self);
        }
        let (Tracked(perm), hold) = self.raw.acquire();
        SpinGuard { lock: self, perm: Tracked(perm), hold }
    }

    /// Dissolves the lock and returns the data, waiting until it is free.
    pub fn into_inner(self) -> (ret: T)
        ensures
            self.inv(ret),
    {
        proof {
            use_type_invariant(&self);
        }
        let SpinLock { cell, raw } = self;
        let Tracked(perm) = raw.into_inner();
        cell.into_inner(Tracked(perm))
    }
}

/// Proof that the lock is held, and the way to the data while it is.
///
/// The lock stays held until [`unlock`](Self::unlock) is called; dropping the
/// guard leaks it, and leaks every thread queued behind it.
pub struct SpinGuard<'a, T, Pred: LockPredicate<T>> {
    lock: &'a SpinLock<T, Pred>,
    perm: Tracked<PointsTo<T>>,
    hold: Hold<PointsTo<T>, CellInv<Pred>>,
}

impl<'a, T, Pred: LockPredicate<T>> SpinGuard<'a, T, Pred> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@.id() == self.lock.cell.id()
        &&& self.hold.instance_id() == self.lock.raw.id()
    }

    /// The lock this guard was taken from.
    pub closed spec fn lock(&self) -> &SpinLock<T, Pred> {
        self.lock
    }

    /// The data as it stands.
    pub closed spec fn view(&self) -> T {
        *self.perm@.value()
    }

    /// Releases the lock and serves the next thread in the queue.
    ///
    /// The data has to satisfy the lock's predicate again: whatever a holder
    /// does to it while holding it, it leaves true what every other thread is
    /// entitled to assume.
    pub fn unlock(self)
        requires
            self.lock().inv(self@),
    {
        proof {
            use_type_invariant(&self);
        }
        let SpinGuard { lock, perm: Tracked(perm), hold } = self;
        lock.raw.release(hold, Tracked(perm));
    }
}

impl<'a, T, Pred: LockPredicate<T>> Deref for SpinGuard<'a, T, Pred> {
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

impl<'a, T, Pred: LockPredicate<T>> DerefMut for SpinGuard<'a, T, Pred> {
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

} // verus!

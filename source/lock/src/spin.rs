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
use core::ops::{Deref, DerefMut};

use vstd::atomic_ghost::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::cell::CellId;
use vstd::invariant::open_atomic_invariant;
#[cfg(verus_only)]
use vstd::pervasive::proof_from_false;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use crate::pred::LockPredicate;
use crate::spin_spec::{CurrentInv, HolderInv};
use crate::spin_tok::TicketToks;

verus! {

/// A place in a lock's queue.
///
/// Handed out by [`RawSpinLock::try_take_ticket`] and given up by entering the
/// lock. A ticket cannot be dropped back into the queue: once a thread has
/// one, the threads behind it wait until it takes the lock and releases it.
pub struct Ticket<V, Pred: LockPredicate<V>> {
    pub(crate) num: u64,
    pub(crate) tok: Tracked<TicketToks::tickets<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> Ticket<V, Pred> {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
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
    pub(crate) tok: Tracked<TicketToks::holding<V, Pred>>,
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
    pub(crate) current: AtomicU64<InstanceId, TicketToks::current<V, Pred>, CurrentInv<V, Pred>>,
    pub(crate) holder: AtomicU64<InstanceId, TicketToks::holder<V, Pred>, HolderInv<V, Pred>>,
    pub(crate) inst: Tracked<TicketToks::Instance<V, Pred>>,
}

impl<V, Pred: LockPredicate<V>> RawSpinLock<V, Pred> {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
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
    pub(crate) cell: PCell<T>,
    pub(crate) raw: RawSpinLock<PointsTo<T>, CellInv<Pred>>,
}

impl<T, Pred: LockPredicate<T>> SpinLock<T, Pred> {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
        self.raw.pred().cell == self.cell.id()
    }

    /// What is true of the data whenever no one holds the lock.
    pub closed spec fn inv(&self, v: T) -> bool {
        self.raw.pred().pred.inv(v)
    }
}

/// Proof that the lock is held, and the way to the data while it is.
///
/// The lock stays held until [`unlock`](Self::unlock) is called; dropping the
/// guard leaks it, and leaks every thread queued behind it.
pub struct SpinGuard<'a, T, Pred: LockPredicate<T>> {
    pub(crate) lock: &'a SpinLock<T, Pred>,
    pub(crate) perm: Tracked<PointsTo<T>>,
    pub(crate) hold: Hold<PointsTo<T>, CellInv<Pred>>,
}

impl<'a, T, Pred: LockPredicate<T>> SpinGuard<'a, T, Pred> {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
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
}

} // verus!
#[verus_verify]
impl<V, Pred: LockPredicate<V>> RawSpinLock<V, Pred> {
    /// Builds a lock, free, holding `v`.
    #[verus_spec(ret =>
        requires
            pred@.inv(v@),
        ensures
            ret.pred() == pred@,
    )]
    pub fn new(v: Tracked<V>, pred: Ghost<Pred>) -> RawSpinLock<V, Pred> {
        proof_decl! {
            let tracked val = v.get();
            let tracked (Tracked(inst), Tracked(cur_tok), Tracked(holder_tok), _, _) =
                TicketToks::Instance::initialize(pred@, val, Some(val));
            let ghost id = inst.id();
        }
        RawSpinLock {
            current: verus_exec_expr! { AtomicU64::new(Ghost(id), 0, Tracked(cur_tok)) },
            holder: verus_exec_expr! { AtomicU64::new(Ghost(id), 0, Tracked(holder_tok)) },
            inst: verus_exec_expr! { Tracked(inst) },
        }
    }

    /// Joins the queue, if a ticket can be had without contention.
    ///
    /// Fails when another thread took a ticket at the same moment, or -- after
    /// `u64::MAX` acquisitions -- when the queue has run out of numbers.
    #[verus_spec(ret =>
        ensures
            ret matches Some(t) ==> t.instance_id() == self.id(),
    )]
    pub fn try_take_ticket(&self) -> Option<Ticket<V, Pred>> {
        proof! {
            use_type_invariant(self);
        }
        let cur;
        open_atomic_invariant!(self.current.atomic_inv.borrow() => pair => {
            let tracked (perm, g) = pair;
            cur = self.current.patomic.load(Tracked(&perm));
            proof { pair = (perm, g); }
        });
        if cur == u64::MAX {
            return None;
        }
        proof_decl! {
            let tracked mut got: Option<TicketToks::tickets<V, Pred>> = None;
        }
        let res;
        open_atomic_invariant!(self.current.atomic_inv.borrow() => pair => {
            let tracked (mut perm, mut g) = pair;
            res = self.current.patomic.compare_exchange(Tracked(&mut perm), cur, cur + 1);
            proof {
                if res is Ok {
                    got = Some(self.inst.borrow().take_ticket(&mut g));
                }
                pair = (perm, g);
            }
        });
        match res {
            Ok(_) => {
                proof_decl! {
                    let tracked tok = match got {
                        Some(tok) => tok,
                        None => proof_from_false(),
                    };
                }
                Some(Ticket { num: cur, tok: verus_exec_expr! { Tracked(tok) } })
            }
            Err(_) => None,
        }
    }

    /// Takes the lock if this ticket is the one being served, and hands the
    /// ticket back otherwise so the caller can ask again.
    #[verus_spec(ret =>
        requires
            ticket.instance_id() == self.id(),
        ensures
            ret matches Ok((v, hold)) ==> self.inv(v@) && hold.instance_id() == self.id(),
            ret matches Err(t) ==> t.instance_id() == self.id(),
    )]
    pub fn try_enter(
        &self,
        ticket: Ticket<V, Pred>,
    ) -> Result<(Tracked<V>, Hold<V, Pred>), Ticket<V, Pred>> {
        proof! {
            use_type_invariant(self);
            use_type_invariant(&ticket);
        }
        let num = ticket.num;
        proof_decl! {
            let tracked mut waiting: Option<TicketToks::tickets<V, Pred>> = Some(ticket.tok.get());
            let tracked mut entered: Option<V> = None;
            let tracked mut hold: Option<TicketToks::holding<V, Pred>> = None;
        }
        let served;
        open_atomic_invariant!(self.holder.atomic_inv.borrow() => pair => {
            let tracked (perm, g) = pair;
            served = self.holder.patomic.load(Tracked(&perm));
            proof {
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
                pair = (perm, g);
            }
        });
        if served == num {
            proof_decl! {
                let tracked v = match entered {
                    Some(v) => v,
                    None => proof_from_false(),
                };
                let tracked h = match hold {
                    Some(h) => h,
                    None => proof_from_false(),
                };
            }
            Ok((verus_exec_expr! { Tracked(v) }, Hold { tok: verus_exec_expr! { Tracked(h) } }))
        } else {
            proof_decl! {
                let tracked t = match waiting {
                    Some(t) => t,
                    None => proof_from_false(),
                };
            }
            Err(Ticket { num, tok: verus_exec_expr! { Tracked(t) } })
        }
    }

    /// Takes the lock, waiting for every thread already in the queue.
    ///
    /// Nothing here bounds how long that is: a holder that never releases
    /// blocks the whole queue for ever, and this crate proves nothing about
    /// whether a waiting thread ever runs. This is one of the three functions
    /// in the crate that Verus accepts without a termination argument.
    #[cfg_attr(verus_only, verifier::exec_allows_no_decreases_clause)]
    #[verus_spec(ret =>
        ensures
            self.inv(ret.0@),
            ret.1.instance_id() == self.id(),
    )]
    pub fn acquire(&self) -> (Tracked<V>, Hold<V, Pred>) {
        let mut ticket: Option<Ticket<V, Pred>> = None;
        #[verus_spec(
            invariant
                ticket matches Some(t) ==> t.instance_id() == self.id(),
        )]
        loop {
            let queued = ticket;
            ticket = None;
            match queued {
                None => {
                    ticket = self.try_take_ticket();
                }
                Some(t) => match self.try_enter(t) {
                    Ok(held) => {
                        return held;
                    }
                    Err(t) => {
                        ticket = Some(t);
                    }
                },
            }
        }
    }

    /// Gives the contents back and serves the next thread in the queue.
    ///
    /// Takes the contents rather than trusting the caller to have left them
    /// alone, so whatever is put back has to satisfy the lock's predicate.
    #[verus_spec(
        requires
            hold.instance_id() == self.id(),
            self.inv(v@),
    )]
    pub fn release(&self, hold: Hold<V, Pred>, v: Tracked<V>) {
        proof! {
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked mut held: Option<TicketToks::holding<V, Pred>> = Some(hold.tok.get());
            let tracked val = v.get();
        }
        open_atomic_invariant!(self.holder.atomic_inv.borrow() => pair => {
            let tracked (mut perm, mut g) = pair;
            proof {
                let tracked t = held.tracked_take();
                let ghost n = t.value();
                self.inst.borrow().leave(n, val, &mut g, t, val);
            }
            self.holder.patomic.fetch_add(Tracked(&mut perm), 1);
            proof { pair = (perm, g); }
        });
    }

    /// Dissolves the lock and returns its contents.
    ///
    /// Queues first: a lock can be consumed while another thread holds it only
    /// if that thread is done, and waiting is the only way to know.
    #[verus_spec(ret =>
        ensures
            self.inv(ret@),
    )]
    pub fn into_inner(self) -> Tracked<V> {
        let (v, _hold) = self.acquire();
        v
    }
}

#[verus_verify]
impl<T, Pred: LockPredicate<T>> SpinLock<T, Pred> {
    /// Builds a lock owning `v`.
    #[verus_spec(ret =>
        requires
            pred@.inv(v),
        ensures
            forall|w: T| ret.inv(w) == pred@.inv(w),
    )]
    pub fn new(v: T, pred: Ghost<Pred>) -> SpinLock<T, Pred> {
        let (cell, perm) = PCell::new(v);
        proof_decl! {
            let ghost cell_pred = CellInv { cell: cell.id(), pred: pred@ };
        }
        let raw = verus_exec_expr! { RawSpinLock::new(perm, Ghost(cell_pred)) };
        SpinLock { cell, raw }
    }

    /// Takes the lock, waiting for every thread already in the queue.
    #[verus_spec(ret =>
        ensures
            ret.lock() == self,
    )]
    pub fn lock(&self) -> SpinGuard<'_, T, Pred> {
        proof! {
            use_type_invariant(self);
        }
        let (perm, hold) = self.raw.acquire();
        SpinGuard { lock: self, perm, hold }
    }

    /// Dissolves the lock and returns the data, waiting until it is free.
    #[verus_spec(ret =>
        ensures
            self.inv(ret),
    )]
    pub fn into_inner(self) -> T {
        proof! {
            use_type_invariant(&self);
        }
        let SpinLock { cell, raw } = self;
        let perm = raw.into_inner();
        cell.into_inner(perm)
    }
}

#[verus_verify]
impl<'a, T, Pred: LockPredicate<T>> SpinGuard<'a, T, Pred> {
    /// Releases the lock and serves the next thread in the queue.
    ///
    /// The data has to satisfy the lock's predicate again: whatever a holder
    /// does to it while holding it, it leaves true what every other thread is
    /// entitled to assume.
    #[verus_spec(
        requires
            self.lock().inv(self@),
    )]
    pub fn unlock(self) {
        proof! {
            use_type_invariant(&self);
        }
        let SpinGuard { lock, perm, hold } = self;
        lock.raw.release(hold, perm);
    }
}

#[verus_verify]
impl<'a, T, Pred: LockPredicate<T>> Deref for SpinGuard<'a, T, Pred> {
    type Target = T;

    #[verus_spec(ret =>
        ensures
            *ret == self@,
    )]
    fn deref(&self) -> &T {
        proof! {
            use_type_invariant(self);
        }
        verus_exec_expr! { self.lock.cell.borrow(Tracked(self.perm.borrow())) }
    }
}

#[verus_verify]
impl<'a, T, Pred: LockPredicate<T>> DerefMut for SpinGuard<'a, T, Pred> {
    #[verus_spec(ret =>
        ensures
            *ret == old(self)@,
            final(self)@ == *final(ret),
            final(self).lock() == old(self).lock(),
    )]
    fn deref_mut(&mut self) -> &mut T {
        proof! {
            use_type_invariant(&*self);
        }
        verus_exec_expr! { self.lock.cell.borrow_mut(Tracked(self.perm.borrow_mut())) }
    }
}

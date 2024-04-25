use core::marker;
use core::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::addr_e::*;
use crate::ptr::*;

verus! {

#[verifier(external_body)]
pub tracked struct LockPermRaw {
    no_copy: NoCopy,
}

pub ghost struct InvRawFn {
    pub invfn: spec_fn(SecSeqByte) -> bool,
}

#[verifier(inline)]
pub open spec fn lockid_to_ptr(lockid: int) -> int {
    lockid
}

#[verifier(inline)]
pub open spec fn ptrid_to_lockid(ptrid: int) -> int {
    ptrid
}

impl InvRawFn {
    pub open spec fn value_invfn<T: VTypeCast<SecSeqByte>>(&self) -> spec_fn(T) -> bool {
        |v: T| (self.invfn)(v.vspec_cast_to())
    }

    pub open spec fn inv<T: VTypeCast<SecSeqByte>>(&self, v: T) -> bool {
        self.value_invfn()(v)
    }

    pub proof fn lemma_inv<T: VTypeCast<SecSeqByte>>(&self)
        ensures
            forall|v: T| #[trigger] self.inv(v) == (self.invfn)(v.vspec_cast_to()),
    {
    }
}

#[derive(SpecSetter, SpecGetter)]
pub ghost struct LockPermToRaw {
    pub locked: bool,
    pub cpu: nat,
    pub points_to: SnpPointsToBytes,
    pub invfn: InvRawFn,
}

impl LockPermToRaw {
    pub open spec fn lockid(&self) -> int {
        ptrid_to_lockid(self.points_to.range().0)
    }

    pub open spec fn ptr_range(&self) -> (int, nat) {
        self.points_to.range()
    }

    pub open spec fn is_clean_lock_for(&self, ptr_range: (int, nat), cpu: nat) -> bool {
        &&& self.ptr_range() == ptr_range
        &&& !self.points_to.wf()
        &&& self.cpu == cpu
        &&& !self.locked
    }
}

impl LockPermRaw {
    pub spec fn view(&self) -> LockPermToRaw;

    #[verifier(external_body)]
    pub proof fn trusted_bind_new<T: VTypeCast<SecSeqByte>>(
        tracked &mut self,
        inv: spec_fn(T) -> bool,
        tracked points_to: SnpPointsToRaw,
    )
        requires
            inv(points_to@.value()),
            old(self)@.ptr_range() == points_to@.range(),
            !old(self)@.locked,
        ensures
            self@.invfn.value_invfn() === inv,
            self@ === old(self)@.spec_set_invfn(self@.invfn).spec_set_points_to(points_to@),
    {
        unimplemented!{}
    }

    pub proof fn tracked_bind_new<T: VTypeCast<SecSeqByte> + IsConstant + WellFormed + SpecSize>(
        tracked &mut self,
        inv: spec_fn(T) -> bool,
        tracked points_to: SnpPointsTo<T>,
    )
        requires
            points_to@.value().is_Some(),
            points_to@.wf_not_null_at(points_to@.id()) || (points_to@.wf() && spec_size::<T>()
                == 0),
            inv(points_to@.get_value()),
            old(self)@.ptr_range() == points_to@.range_id(),
            !old(self)@.locked,
        ensures
            self@.invfn.value_invfn() === inv,
            self@ === old(self)@.spec_set_invfn(self@.invfn).spec_set_points_to(
                points_to@.vspec_cast_to(),
            ),
            self@.wf(),
    {
        let tracked raw_points_to = points_to.tracked_into_raw();
        self.trusted_bind_new(inv, raw_points_to);
        self@.invfn.lemma_inv::<T>();
        assert((self@.invfn.invfn)(raw_points_to@.bytes()))
    }
}

impl LockPermToRaw {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        &&& if self.points_to.range().1 > 0 {
            // Memory access
            self.points_to.wf_not_null(self.points_to.range())
        } else {
            // Other locks (e.g., console or other devices)
            self.points_to.wf()
        }
        &&& (self.invfn.invfn)(self.points_to.bytes())
    }

    #[verifier(inline)]
    pub open spec fn wf_for(&self, lockid: int, range: (int, nat)) -> bool {
        &&& self.wf()
        &&& self.lockid() == lockid
        &&& self.points_to.range() === range
    }

    pub open spec fn is_unlocked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool {
        &&& !self.locked
        &&& self.cpu == cpu
        &&& self.wf_for(lockid, range)
    }

    pub open spec fn is_locked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool {
        &&& self.locked
        &&& self.cpu == cpu
        &&& self.wf_for(lockid, range)
    }
}

pub trait MapRawLockTrait {
    spec fn is_locked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool;

    spec fn is_unlocked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool;

    spec fn inv(&self, cpu: nat) -> bool;

    spec fn inv_locked(&self, cpu: nat, lockid: Set<int>) -> bool;

    spec fn contains_lock(&self, lockid: int, ptr_range: (int, nat)) -> bool;

    spec fn updated_lock(&self, prev: &Self, locks: Set<int>) -> bool;

    spec fn contains_clean_locks(&self, cpu: nat, locks: Map<int, (int, nat)>) -> bool;

    proof fn lemma_lock_update_auto()
        ensures
            forall|prev: &Self, cur: &Self, next: &Self, locks1: Set<int>, locks2: Set<int>|
                (#[trigger] cur.updated_lock(prev, locks1) && #[trigger] next.updated_lock(
                    cur,
                    locks2,
                )) ==> next.updated_lock(prev, locks1.union(locks2)),
    ;
}

pub trait MapLockContains<T> {
    spec fn contains_vlock(&self, lock: VSpinLock<T>) -> bool;
}

pub type LockMap = Map<int, LockPermRaw>;

impl MapRawLockTrait for LockMap {
    #[verifier(inline)]
    open spec fn is_locked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool {
        &&& self.contains_key(lockid)
        &&& (#[trigger] self[lockid])@.is_locked(cpu, lockid, range)
    }

    #[verifier(inline)]
    open spec fn is_unlocked(&self, cpu: nat, lockid: int, range: (int, nat)) -> bool {
        &&& self.contains_key(lockid)
        &&& (#[trigger] self[lockid])@.is_unlocked(cpu, lockid, range)
    }

    open spec fn inv(&self, cpu: nat) -> bool {
        self.inv_locked(cpu, set![])
    }

    open spec fn inv_locked(&self, cpu: nat, locks: Set<int>) -> bool {
        &&& forall|id: int|
            self.contains_key(id) && !locks.contains(id) ==> (#[trigger] self[id])@.is_unlocked(
                cpu,
                id,
                self[id]@.points_to.range(),
            )
        &&& forall|id: int|
            self.contains_key(id) && locks.contains(id) ==> (#[trigger] self[id])@.is_locked(
                cpu,
                id,
                self[id]@.points_to.range(),
            )
    }

    open spec fn contains_lock(&self, lockid: int, ptr_range: (int, nat)) -> bool {
        &&& self.contains_key(lockid)
        &&& self[lockid]@.points_to.range() === ptr_range
    }

    open spec fn updated_lock(&self, prev: &Self, locks: Set<int>) -> bool {
        &&& prev.dom() =~~= self.dom()
        &&& (forall|id: int|
            (locks.contains(id) && #[trigger] self.contains_key(id)) ==> (
            self[id])@.points_to.only_val_updated(prev[id]@.points_to))
        &&& (forall|id: int|
            (!locks.contains(id) && #[trigger] self.contains_key(id)) ==> (self[id]) === prev[id])
    }

    open spec fn contains_clean_locks(&self, cpu: nat, locks: Map<int, (int, nat)>) -> bool {
        &&& forall|id: int|
            locks.contains_key(id) ==> (#[trigger] self[id])@.is_clean_lock_for(locks[id], cpu)
                && self.contains_key(id)
        &&& forall|id: int| locks.contains_key(id) ==> #[trigger] self.contains_key(id)
    }

    proof fn lemma_lock_update_auto() {
        assert forall|prev: &Self, cur: &Self, next: &Self, locks1: Set<int>, locks2: Set<int>|
            (#[trigger] cur.updated_lock(prev, locks1) && #[trigger] next.updated_lock(
                cur,
                locks2,
            )) implies next.updated_lock(prev, locks1.union(locks2)) by {
            let locks = locks1.union(locks2);
            assert forall|id: int|
                locks.contains(id) && prev.contains_key(id) implies next.contains_key(id) && (
            #[trigger] next[id])@.points_to.only_val_updated(prev[id]@.points_to) by {
                if (locks1.contains(id)) {
                    assert(cur[id]@.points_to.only_val_updated(prev[id]@.points_to));
                } else {
                    assert(cur[id] === prev[id]);
                    assert(cur[id]@.points_to.only_val_updated(prev[id]@.points_to));
                }
            }
            assert forall|id: int|
                !locks.contains(id) && prev.contains_key(id) implies #[trigger] next[id]
                === prev[id] && next.contains_key(id) by {
                assert(!locks1.contains(id));
                assert(!locks2.contains(id));
                assert(cur[id] === prev[id]);
                assert(next[id] === cur[id]);
            }
            // VERUS bugs?: ASSERTIONS are required to pass verification.

            assert(forall|id: int|
                locks.contains(id) && prev.contains_key(id) ==> next.contains_key(id) && (
                #[trigger] next[id])@.points_to.only_val_updated(prev[id]@.points_to));
            assert(forall|id: int|
                !locks.contains(id) && prev.contains_key(id) ==> #[trigger] next[id] === prev[id]
                    && next.contains_key(id));
        }
    }
}

impl<T> MapLockContains<T> for Map<int, LockPermRaw> {
    #[verifier(inline)]
    open spec fn contains_vlock(&self, lock: VSpinLock<T>) -> bool {
        &&& self.contains_key(lock.lockid())
        &&& self[lock.lockid()]@.points_to.range() === lock.ptr_range()
    }
}

} // verus!

use core::marker;
use core::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::addr_e::*;
use crate::ptr::*;

verus! {

#[verifier(external_body)]
pub struct SpinLock {
    current: AtomicU64,
    holder: AtomicU64,
}

} // verus!
verus! {

impl IsConstant for SpinLock {
    open spec fn is_constant(&self) -> bool;

    open spec fn is_constant_to(&self, vmpl: nat) -> bool;
}

impl WellFormed for SpinLock {
    open spec fn wf(&self) -> bool;
}

impl VTypeCast<SecSeqByte> for SpinLock {
    open spec fn vspec_cast_to(self) -> SecSeqByte;
}

impl SpecSize for SpinLock {
    open spec fn spec_size_def() -> nat;
}

impl SpinLock {
    pub spec fn id(self) -> int;

    #[verifier(external_body)]
    pub const fn new() -> (ret: Self) {
        SpinLock { current: AtomicU64::new(1), holder: AtomicU64::new(1) }
    }

    pub open spec fn ensures_lock(
        &self,
        oldp: LockPermToRaw,
        newp: LockPermToRaw,
        ret_perm: SnpPointsToBytes,
    ) -> bool {
        &&& newp === oldp.spec_set_locked(true)
        &&& ret_perm.snp() === oldp.points_to.snp()
        &&& ret_perm.range() === oldp.points_to.range()
        &&& ret_perm.wf()
        &&& (oldp.invfn.invfn)(ret_perm.bytes())
    }

    pub open spec fn ensures_lock_value<
        T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>,
    >(&self, oldp: LockPermToRaw, newp: LockPermToRaw, ret_perm: SnpPointsToData<T>) -> bool {
        &&& newp === oldp.spec_set_locked(true)
        &&& ret_perm.snp() === oldp.points_to.snp()
        &&& ret_perm.range_id() === oldp.points_to.range()
        &&& ret_perm.wf()
        &&& ret_perm.value().is_Some()
        &&& oldp.invfn.inv(ret_perm.get_value())
    }

    pub open spec fn ensures_unlock(
        &self,
        oldp: LockPermToRaw,
        newp: LockPermToRaw,
        points_to: SnpPointsToBytes,
    ) -> bool {
        &&& newp === oldp.spec_set_locked(false).spec_set_points_to(points_to)
    }

    #[verifier(external_body)]
    pub fn trylock(
        &self,
        Tracked(lockperm): Tracked<&mut LockPermRaw>,
        Tracked(core): Tracked<&CoreIdPerm>,
    ) -> (ret: Option<Tracked<SnpPointsToRaw>>)
        requires
            old(lockperm)@.is_unlocked(core@.cpu, self.id(), old(lockperm)@.points_to.range()),
        ensures
            ret.is_Some() ==> self.ensures_lock(old(lockperm)@, lockperm@, ret.get_Some_0()@@),
            ret.is_None() ==> lockperm === old(lockperm),
    {
        if self.unverified_trylock() {
            Some(Tracked::assume_new())
        } else {
            None
        }
    }

    #[verifier(external_body)]
    pub fn unlock(
        &self,
        Tracked(lockperm): Tracked<&mut LockPermRaw>,
        Tracked(perm): Tracked<SnpPointsToRaw>,
        Tracked(core): Tracked<&CoreIdPerm>,
    )
        requires
            old(lockperm)@.is_locked(core@.cpu, self.id(), perm@.range()),
            perm@.wf(),
        ensures
            self.ensures_unlock(old(lockperm)@, lockperm@, perm@),
    {
        self.unverified_unlock();
    }

    // requires: check no deadlock
    #[verifier(external)]
    fn unverified_trylock(&self) -> bool {
        let ticket: u64 = self.current.fetch_add(1, Ordering::Relaxed);
        loop {
            let h: u64 = self.holder.load(Ordering::Acquire);
            if h == ticket {
                break ;
            }
        }
        true
    }

    #[verifier(external)]
    fn unverified_unlock(&self) {
        self.holder.fetch_add(1, Ordering::Release);
    }
}

#[verifier(external_body)]
pub fn fence() {
    core::sync::atomic::fence(Ordering::SeqCst);
}

} // verus!

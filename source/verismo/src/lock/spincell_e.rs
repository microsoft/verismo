use core::marker;
use core::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::addr_e::*;
use crate::ptr::*;
use crate::vcell::*;

verus! {

impl SpinLock {
    // requires: check no deadlock
    pub fn lock(
        &self,
        Tracked(lockperm): Tracked<LockPermRaw>,
        Tracked(core): Tracked<&CoreIdPerm>,
    ) -> (perm: (Tracked<LockPermRaw>, Tracked<SnpPointsToRaw>))
        requires
            lockperm@.is_unlocked(core@.cpu, self.id(), lockperm@.points_to.range()),
        ensures
            self.ensures_lock(lockperm@, perm.0@@, perm.1@@),
    {
        let got = false;
        let mut perm: Tracked<SnpPointsToRaw>;
        let tracked mut tmplockperm = lockperm;
        loop
            invariant_except_break
                tmplockperm@.is_unlocked(core@.cpu, self.id(), lockperm@.points_to.range()),
                tmplockperm === lockperm,
            ensures
                self.ensures_lock((lockperm)@, tmplockperm@, perm@@),
        {
            if let Some(tmpperm) = self.trylock(Tracked(&mut tmplockperm), Tracked(core)) {
                perm = tmpperm;
                break ;
            }
        }
        (Tracked(tmplockperm), perm)
    }
}

} // verus!
verismo_simple! {
#[derive(SpecGetter, SpecSetter)]
pub struct VSpinLock<T> {
    lock: SpinLock,
    data: crate::vcell::VCell<T>,
}
}

verus! {

impl<T> VSpinLock<T> {
    #[verifier(inline)]
    pub open spec fn lockid(&self) -> int {
        self.spec_lock().id()
    }

    #[verifier(inline)]
    pub open spec fn ptrid(&self) -> int {
        lockid_to_ptr(self.lockid())
    }

    #[verifier(inline)]
    pub open spec fn ptr_range(self) -> (int, nat) {
        (self.ptrid(), spec_size::<T>())
    }
}

} // verus!
verus! {

impl<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>> VSpinLock<T> {
    #[verifier(external_body)]
    pub fn ptr(&self) -> (ret: SnpPPtr<T>)
        requires
            self.is_constant(),
        ensures
            ret.id() == self.ptrid(),
            ret.is_constant(),
    {
        let addr = unsafe { &self.data as *const _ as usize };
        SnpPPtr::from_usize(addr)
    }

    pub open spec fn lock_requires(&self, cpu: nat, lockperm: LockPermToRaw) -> bool {
        &&& (lockperm).is_unlocked(cpu, self.lockid(), self.ptr_range())
        &&& self.is_constant()
    }

    pub open spec fn lock_default_mem_requires(&self, cpu: nat, lockperm: LockPermToRaw) -> bool {
        &&& self.lock_requires(cpu, lockperm)
        &&& lockperm.points_to.snp() === SwSnpMemAttr::spec_default()
    }

    pub open spec fn unlock_requires(
        &self,
        cpu: nat,
        lockperm: LockPermToRaw,
        memperm: SnpPointsToData<T>,
    ) -> bool {
        &&& (lockperm).is_locked(cpu, self.lockid(), self.ptr_range())
        &&& (lockperm).invfn.inv(memperm.get_value())
        &&& memperm.value.is_Some()
        &&& memperm.wf_at(self.lockid())
        &&& self.is_constant()
    }

    pub open spec fn unlock_default_mem_requires(
        &self,
        cpu: nat,
        lockperm: LockPermToRaw,
        memperm: SnpPointsToData<T>,
    ) -> bool {
        &&& self.unlock_requires(cpu, lockperm, memperm)
        &&& lockperm.points_to.snp() === SwSnpMemAttr::spec_default()
    }

    pub open spec fn ensures_lock(
        &self,
        oldp: LockPermToRaw,
        newp: LockPermToRaw,
        ret_perm: SnpPointsToData<T>,
    ) -> bool {
        &&& self.spec_lock().ensures_lock_value(oldp, newp, ret_perm)
    }

    pub open spec fn ensures_unlock(
        &self,
        oldp: LockPermToRaw,
        newp: LockPermToRaw,
        in_perm: SnpPointsToData<T>,
    ) -> bool {
        &&& newp === oldp.spec_set_locked(false).spec_set_points_to(in_perm.vspec_cast_to())
        &&& newp.wf()
    }

    pub fn acquire(
        &self,
        Tracked(lockperm): Tracked<LockPermRaw>,
        Tracked(core): Tracked<&CoreIdPerm>,
    ) -> (ret: (SnpPPtr<T>, Tracked<SnpPointsTo<T>>, Tracked<LockPermRaw>))
        requires
            self.lock_requires(core@.cpu, lockperm@),
        ensures
            self.ensures_lock((lockperm)@, ret.2@@, ret.1@@),
            ret.0.id() === self.ptrid(),
            ret.0.is_constant(),
            ret.1@@.wf_at(ret.0.id()),
    {
        proof {
            lockperm@.invfn.lemma_inv::<T>();
        }
        let (lockperm, rawperm) = self.lock.lock(Tracked(lockperm), Tracked(core));
        let Tracked(rawperm) = rawperm;
        let tracked ptrperm = rawperm.trusted_into();
        (self.ptr().clone(), Tracked(ptrperm), lockperm)
    }

    pub fn acquire_(
        &self,
        Tracked(lockperms): Tracked<&mut Map<int, LockPermRaw>>,
        Tracked(core): Tracked<&CoreIdPerm>,
    ) -> (ret: (SnpPPtr<T>, Tracked<SnpPointsTo<T>>))
        requires
            old(lockperms).contains_key(self.lockid()),
            self.lock_requires(core@.cpu, old(lockperms)[self.lockid()]@),
        ensures
            *lockperms =~~= old(lockperms).insert(
                self.spec_lock().id(),
                (lockperms)[self.spec_lock().id()],
            ),
            self.ensures_lock(old(lockperms)[self.lockid()]@, (lockperms)[self.lockid()]@, ret.1@@),
            self.unlock_requires(core@.cpu, lockperms[self.lockid()]@, ret.1@@),
            ret.0.id() === self.ptrid(),
            ret.0.is_constant(),
    {
        let tracked mut lockperm = lockperms.tracked_remove(self.spec_lock().id());
        let (ptr, perm, lockperm) = self.acquire(Tracked(lockperm), Tracked(core));
        let Tracked(lockperm) = lockperm;
        proof {
            lockperms.tracked_insert(self.spec_lock().id(), lockperm);
        }
        (ptr, perm)
    }

    pub fn release(
        &self,
        Tracked(lockperm): Tracked<&mut LockPermRaw>,
        Tracked(perm): Tracked<SnpPointsTo<T>>,
        Tracked(core): Tracked<&CoreIdPerm>,
    )
        requires
            self.unlock_requires(core@.cpu, old(lockperm)@, perm@),
        ensures
            self.ensures_unlock(old(lockperm)@, lockperm@, perm@),
            lockperm@.wf(),
    {
        proof {
            lockperm@.invfn.lemma_inv::<T>();
        }
        let tracked rawperm = perm.trusted_into_raw();
        self.lock.unlock(Tracked(lockperm), Tracked(rawperm), Tracked(core));
    }

    pub const fn new(value: T) -> Self {
        VSpinLock { lock: SpinLock::new(), data: VCell::new(value) }
    }

    pub fn release_(
        &self,
        Tracked(lockperms): Tracked<&mut Map<int, LockPermRaw>>,
        Tracked(perm): Tracked<SnpPointsTo<T>>,
        Tracked(core): Tracked<&CoreIdPerm>,
    )
        requires
            old(lockperms).contains_key(self.lockid()),
            self.unlock_requires(core@.cpu, old(lockperms)[self.lockid()]@, perm@),
        ensures
            self.ensures_unlock(
                old(lockperms)[self.spec_lock().id()]@,
                lockperms[self.spec_lock().id()]@,
                perm@,
            ),
            *lockperms =~~= old(lockperms).insert(
                self.spec_lock().id(),
                lockperms[self.spec_lock().id()],
            ),
    {
        let tracked mut lockperm = lockperms.tracked_remove(self.spec_lock().id());
        self.release(Tracked(&mut lockperm), Tracked(perm), Tracked(core));
        proof {
            lockperms.tracked_insert(self.spec_lock().id(), lockperm);
        }
    }
}

} // verus!

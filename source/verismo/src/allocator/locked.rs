use super::*;
use crate::registers::CoreIdPerm;
use crate::debug::VPrintAtLevel;

verus! {

impl VSpinLock<VeriSMoAllocator> {
    pub open spec fn lock_alloc_requires(&self, cpu: nat, alloc_lockperm: LockPermToRaw) -> bool {
        &&& self.lock_default_mem_requires(cpu, alloc_lockperm)
        &&& alloc_lockperm.invfn.value_invfn() === VeriSMoAllocator::invfn()
    }

    pub fn alloc_(
        &self,
        size: usize,
        align: usize,
        Tracked(alloc_lockperm): Tracked<LockPermRaw>,
        Tracked(coreid): Tracked<&CoreIdPerm>,
    ) -> (res: (Result<(usize, Tracked<SnpPointsToRaw>), ()>, Tracked<LockPermRaw>))
        requires
            self.is_constant(),
            size >= VeriSMoAllocator::spec_minsize(),
            self.lock_alloc_requires(coreid@.cpu, alloc_lockperm@),
            spec_bit64_is_pow_of_2(align as int),
        ensures
            self.lock_alloc_requires(coreid@.cpu, res.1@@),
            res.0.is_Ok() ==> talloc_valid_ptr(size, res.0.get_Ok_0()) && (
            res.0.get_Ok_0().0 as int) % (align as int) == 0,
    {
        let tracked alloc_lockperm = alloc_lockperm;
        (new_strlit("\n new")).leak_debug();
        let (ptr, Tracked(mut allocperm), Tracked(alloc_lockperm)) = self.acquire(
            Tracked(alloc_lockperm),
            Tracked(coreid),
        );
        (new_strlit(":")).leak_debug();
        let mut allocator = ptr.take(Tracked(&mut allocperm));
        let mut size = size;
        let result = allocator.alloc_inner(size, align);
        ptr.put(Tracked(&mut allocperm), allocator);
        self.release(Tracked(&mut alloc_lockperm), Tracked(allocperm), Tracked(coreid));
        if let Some((addr, perm)) = result {
            (new_strlit(": "), addr).leak_debug();
            (Ok((addr, perm)), Tracked(alloc_lockperm))
        } else {
            (Err(()), Tracked(alloc_lockperm))
        }
    }

    pub fn alloc_aligned(
        &self,
        size: usize,
        align: usize,
        Tracked(alloc_lockperm0): Tracked<&mut Map<int, LockPermRaw>>,
        Tracked(coreid): Tracked<&CoreIdPerm>,
    ) -> (res: Result<(usize, Tracked<SnpPointsToRaw>), ()>)
        requires
            self.is_constant(),
            size >= VeriSMoAllocator::spec_minsize(),
            old(alloc_lockperm0).contains_key(0),
            self.lock_alloc_requires(coreid@.cpu, old(alloc_lockperm0)[0]@),
            spec_bit64_is_pow_of_2(align as int),
        ensures
            alloc_lockperm0.contains_key(0),
            self.lock_alloc_requires(coreid@.cpu, alloc_lockperm0[0]@),
            res.is_Ok() ==> talloc_valid_ptr(size, res.get_Ok_0()) && (res.get_Ok_0().0 as int) % (
            align as int) == 0,
    {
        let tracked alloc_perm = alloc_lockperm0.tracked_remove(0);
        let (ret, Tracked(alloc_perm)) = self.alloc_(
            size,
            align,
            Tracked(alloc_perm),
            Tracked(coreid),
        );
        proof {
            alloc_lockperm0.tracked_insert(0, alloc_perm);
        }
        ret
    }

    pub fn dealloc_(
        &self,
        addr: usize,
        size: usize,
        Tracked(memperm): Tracked<SnpPointsToRaw>,
        Tracked(alloc_lockperm): Tracked<LockPermRaw>,
        Tracked(coreid): Tracked<&CoreIdPerm>,
    ) -> (newlockperm: Tracked<LockPermRaw>)
        requires
            self.is_constant(),
            memperm@.wf_default((addr as int, size as nat)),
            size > 0,
            size >= VeriSMoAllocator::spec_minsize(),
            self.lock_alloc_requires(coreid@.cpu, alloc_lockperm@),
        ensures
            self.lock_alloc_requires(coreid@.cpu, newlockperm@@),
    {
        let tracked mut memperm = memperm;
        let tracked mut alloc_lockperm = alloc_lockperm;
        let (ptr, Tracked(mut allocperm), Tracked(mut alloc_lockperm)) = self.acquire(
            Tracked(alloc_lockperm),
            Tracked(coreid),
        );
        let mut allocator = ptr.take(Tracked(&mut allocperm));
        assert(alloc_lockperm@.invfn.inv(allocator));
        assert(VeriSMoAllocator::invfn()(allocator));
        ((new_strlit("\ndealloc: "), addr), size).leak_debug();
        allocator.dealloc_inner(addr, size, Tracked(memperm));
        ptr.put(Tracked(&mut allocperm), allocator);
        self.release(Tracked(&mut alloc_lockperm), Tracked(allocperm), Tracked(coreid));
        Tracked(alloc_lockperm)
    }
}

} // verus!

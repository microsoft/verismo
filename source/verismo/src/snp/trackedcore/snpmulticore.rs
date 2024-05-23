use super::*;
use crate::global::{spec_CONSOLE, IsConsole, *};
use crate::lock::*;
use crate::pgtable_e::*;
use crate::ptr::SnpPointsToRaw;

verus! {

#[derive(SpecGetter, SpecSetter)]
pub tracked struct SnpCoreSharedMem {
    pub snpcore: SnpCore,
    pub lockperms: Map<int, LockPermRaw>,
}

impl SnpCoreSharedMem {
    pub open spec fn inv(&self) -> bool {
        &&& self.snpcore.inv()
        &&& self.lockperms.inv(self.snpcore.cpu())
        &&& contains_CONSOLE(self.lockperms)
        &&& contains_ALLOCATOR(self.lockperms)
        &&& contains_PT(self.lockperms)
        &&& self.wf_pt()
    }

    pub open spec fn inv_stage_common(&self) -> bool {
        &&& self.inv()
    }

    pub open spec fn inv_stage_verismo(&self) -> bool {
        &&& self.inv()
        &&& contains_OSMEM(self.lockperms)
        &&& contains_RICHOS_VMSA(self.lockperms)
        &&& contains_PCR(self.lockperms)
    }

    pub open spec fn inv_stage_ap_wait(&self) -> bool {
        self.inv_stage_verismo()
    }

    pub open spec fn inv_stage_pcr(&self) -> bool {
        &&& self.inv()
        &&& contains_PCR(self.lockperms)
    }

    pub open spec fn wf_top_pt(&self) -> bool {
        let cr3_u64: u64 = self.snpcore.regs[RegName::Cr3].val::<u64_s>().vspec_cast_to();
        let top_pte = self.pte_perms()[top_lvl_idx()].val();
        &&& top_pte.value == static_cr3_value()
        &&& cr3_u64 == static_cr3_value()
    }

    pub open spec fn wf_pt(&self) -> bool {
        &&& self.wf_top_pt()
        &&& wf_ptes(self.pte_perms())
    }

    pub open spec fn pte_perms(&self) -> PtePerms {
        self.lockperms[spec_PT_lockid()]@.points_to.value::<TrackedPTEPerms>()@
    }

    pub open spec fn inv_core(&self, core: nat) -> bool {
        &&& self.inv()
        &&& self.snpcore.cpu() == core
    }

    pub open spec fn only_lock_reg_updated(
        &self,
        prev: Self,
        regs: Set<RegName>,
        locks: Set<int>,
    ) -> bool {
        &&& self.lockperms.updated_lock(&prev.lockperms, locks)
        &&& self.snpcore.only_reg_updated(prev.snpcore, regs)
    }

    //#[verifier(inline)]
    pub open spec fn only_lock_reg_coremode_updated(
        &self,
        prev: Self,
        regs: Set<RegName>,
        locks: Set<int>,
    ) -> bool {
        &&& self.lockperms.updated_lock(&prev.lockperms, locks)
        &&& self.snpcore.only_reg_coremode_updated(prev.snpcore, regs)
    }

    pub proof fn lemma_update_prop_auto()
        ensures
            forall|prev: Self, cur: Self, next: Self, regs1, regs2|
                (#[trigger] cur.snpcore.reg_updated(prev.snpcore, regs1)
                    && #[trigger] next.snpcore.reg_updated(cur.snpcore, regs2))
                    ==> next.snpcore.reg_updated(prev.snpcore, regs1.union(regs2)),
            forall|prev: Self, cur: Self, next: Self, locks1: Set<int>, locks2: Set<int>|
                (#[trigger] cur.lockperms.updated_lock(&prev.lockperms, locks1)
                    && #[trigger] next.lockperms.updated_lock(&cur.lockperms, locks2))
                    ==> next.lockperms.updated_lock(&prev.lockperms, locks1.union(locks2)),
    {
        LockMap::lemma_lock_update_auto();
        SnpCore::lemma_regs_update_auto();
    }

    pub proof fn lemma_update_prop(
        &self,
        cur: Self,
        next: Self,
        regs1: Set<RegName>,
        locks1: Set<int>,
        regs2: Set<RegName>,
        locks2: Set<int>,
    )
        requires
            #[trigger] cur.only_lock_reg_coremode_updated(*self, regs1, locks1),
            #[trigger] next.only_lock_reg_coremode_updated(cur, regs2, locks2),
        ensures
            next.only_lock_reg_coremode_updated(*self, regs1.union(regs2), locks1.union(locks2)),
            Set::<int>::empty().union(set![]) =~~= set![],
            regs1.union(regs2) =~~= regs2.union(regs1),
            locks1.union(locks2) =~~= locks2.union(locks1),
            forall|s: Set<RegName>| s.union(s) =~~= s,
            forall|s: Set<int>| s.union(s) =~~= s,
            forall|s: Set<RegName>| s.union(set![]) =~~= s,
            forall|s: Set<int>| s.union(set![]) =~~= s,
            forall|s: Set<RegName>| set![].union(s) =~~= s,
            forall|s: Set<int>| set![].union(s) =~~= s,
    {
        Self::lemma_update_prop_auto();
    }
}

} // verus!
verus! {

pub tracked struct SnpCoreConsole {
    pub snpcore: SnpCore,
    pub console: Map<int, SnpPointsToRaw>,
}

pub open spec fn snpcore_console_wf(snpcore: SnpCore, console: SnpPointsToRaw) -> bool {
    &&& snpcore.inv()
    &&& console.is_console()
}

impl SnpCoreConsole {
    pub open spec fn console(&self) -> SnpPointsToRaw {
        self.console[0]
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.console.contains_key(0)
        &&& snpcore_console_wf(self.snpcore, self.console[0])
    }

    pub open spec fn wf_core(&self, core: nat) -> bool {
        &&& self.wf()
        &&& self.snpcore.cpu() == core
    }

    #[verifier(inline)]
    pub open spec fn only_console_reg_coremode_updated(
        &self,
        prev: Self,
        regs: Set<RegName>,
    ) -> bool {
        &&& self.console.contains_key(0)
        &&& self.console[0]@.only_val_updated(prev.console[0]@)
        &&& self.snpcore.only_reg_coremode_updated(prev.snpcore, regs)
    }
}

} // verus!

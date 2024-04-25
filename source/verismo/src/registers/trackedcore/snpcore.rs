use super::*;
use crate::pgtable_e::{static_cr3_value, PTE};

verus! {

pub type RegMap = Map<RegName, RegisterPerm>;

#[derive(SpecGetter, SpecSetter)]
pub tracked struct SnpCore {
    pub coreid: CoreIdPerm,
    pub vmpl: nat,
    pub cpu: nat,
    pub regs: Map<RegName, RegisterPerm>,
}

impl SnpCore {
    #[verifier(inline)]
    pub open spec fn cpu(&self) -> nat {
        self.coreid@.cpu
    }

    pub open spec fn update_reg_coremode(self, prev: Self) -> bool {
        self === prev.spec_set_coreid(self.coreid).spec_set_regs(self.regs)
    }

    pub open spec fn inv_reg_cpu(&self) -> bool {
        let regs = self.regs;
        let coreid = self.coreid;
        let cr3_pte: u64 = regs[RegName::Cr3].val::<u64_s>().vspec_cast_to();
        &&& coreid@.vmpl == self.vmpl
        &&& coreid@.run
        &&& coreid@.cpu == self.cpu
        &&& forall|id: RegName| regs.contains_key(id)
        &&& forall|id: RegName| (#[trigger] regs[id]).cpu() == coreid@.cpu
        &&& forall|id: RegName| (#[trigger] regs[id]).id() === id
        &&& forall|id: RegName| (#[trigger] regs[id]).wf()
        &&& regs[RegName::MSR(MSR_GHCB_BASE)].shared() == true
        &&& forall|id: RegName|
            id !== RegName::MSR(MSR_GHCB_BASE) ==> !(#[trigger] regs[id]).shared()
        &&& regs[RegName::GdtrBaseLimit].val::<crate::snp::cpu::Gdtr>().is_constant()
        &&& regs[RegName::IdtrBaseLimit].val::<crate::boot::idt::Idtr>().is_constant()
        &&& regs[RegName::XCr0].val::<u64_s>().is_constant()
        &&& regs[RegName::Cr0].val::<u64_s>().is_constant()
        &&& regs[RegName::Cr1].val::<u64_s>().is_constant()
        &&& regs[RegName::Cr2].val::<u64_s>().is_constant()
        &&& regs[RegName::Cr3].val::<u64_s>().is_constant()
        &&& regs[RegName::Cr4].val::<u64_s>().is_constant()
        &&& regs[RegName::Cs].val::<u16_s>().is_constant()
        &&& regs[RegName::MSR(MSR_EFER_BASE)].val::<u64_s>().is_constant()
        &&& cr3_pte == static_cr3_value()
    }

    pub open spec fn ghcb_value(&self) -> u64 {
        self.regs[RegName::MSR(MSR_GHCB_BASE)].val::<u64_s>().vspec_cast_to()
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.inv_reg_cpu()
        &&& self.vmpl == 0
    }

    #[verifier(inline)]
    pub open spec fn last_ghcb_req(&self) -> nat {
        (*self).ghcbmsr_msgs().last().0
    }

    #[verifier(inline)]
    pub open spec fn last_ghcb_resp(&self) -> nat {
        (*self).ghcbmsr_msgs().last().1
    }

    #[verifier(inline)]
    pub open spec fn last_ghcbmem_req(&self) -> crate::snp::ghcb::GhcbPage {
        (*self).ghcbmem_msgs().last().1.vspec_cast_to()
    }

    #[verifier(inline)]
    pub open spec fn last_ghcbmem_resp(&self) -> crate::snp::ghcb::GhcbPage {
        (*self).ghcbmem_msgs().last().2.vspec_cast_to()
    }

    #[verifier(inline)]
    pub open spec fn ghcbmsr_msgs(&self) -> Seq<(nat, nat)> {
        (*self).coreid@.sent_ghcb_msrs
    }

    #[verifier(inline)]
    pub open spec fn ghcbmem_msgs(&self) -> Seq<((int, nat), SecSeqByte, SecSeqByte)> {
        (*self).coreid@.sent_mem
    }

    pub open spec fn reg_updated(self, prev: Self, regs: Set<RegName>) -> bool {
        &&& forall|i| !regs.contains(i) ==> #[trigger] self.regs[i] === prev.regs[i]
    }

    #[verifier(inline)]
    pub open spec fn only_reg_updated(self, prev: Self, regs: Set<RegName>) -> bool {
        &&& self.reg_updated(prev, regs)
        &&& (regs.is_empty()) ==> self.regs === prev.regs
        &&& self === prev.spec_set_regs(self.regs)
    }

    #[verifier(inline)]
    pub open spec fn only_reg_coremode_updated(self, prev: Self, regs: Set<RegName>) -> bool {
        &&& self === prev.spec_set_coreid(self.coreid).spec_set_regs(self.regs)
        &&& self.reg_updated(prev, regs)
    }

    pub proof fn lemma_regs_update_auto()
        ensures
            forall|prev: Self, cur: Self, next: Self, regs1, regs2|
                (#[trigger] cur.reg_updated(prev, regs1) && #[trigger] next.reg_updated(cur, regs2))
                    ==> next.reg_updated(prev, regs1.union(regs2)),
    {
        assert forall|prev: Self, cur: Self, next: Self, regs1, regs2|
            (#[trigger] cur.reg_updated(prev, regs1) && #[trigger] next.reg_updated(
                cur,
                regs2,
            )) implies next.reg_updated(prev, regs1.union(regs2)) by {
            let regs = regs1.union(regs2);
            assert forall|i| !regs.contains(i) implies #[trigger] next.regs[i] === prev.regs[i] by {
                assert(!regs1.contains(i));
                assert(cur.regs[i] === prev.regs[i]);
            }
        }
    }
}

} // verus!

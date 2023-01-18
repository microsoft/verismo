use super::*;
use crate::arch::attack::*;
use crate::arch::pgtable::SpecPageTableEntry;
verus! {
    impl Model1Eq for Archx64 {
        open spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool {
            &&& self.spec_memdb().model1_eq(&other.spec_memdb(), memid)
            &&& equal(self.spec_regdb(), other.spec_regdb())
            &&& equal(self.spec_entities(), other.spec_entities())
            &&& equal(self.spec_cpu(), other.spec_cpu())
        }
    }
}

verus! {
    impl Archx64 {
        pub open spec fn inv_regdb(&self, cpu: CPU, memid: MemID) -> bool {
            &&& self.spec_regdb()[CpuMemID(cpu, memid)].reg_inv()
            &&& self.spec_memdb().spec_g_page_table(memid).l0_entry(memid) ===
                    SpecPageTableEntry::new_val(
                        (self.spec_regdb()[CpuMemID(cpu, memid)])
                                        .spec_index(RegName::Cr3) as int)
        }

        pub open spec fn inv_regdb_any_cpu(&self, memid: MemID) -> bool {
            forall |cpu| (#[trigger]self.inv_regdb(cpu, memid))
        }

        pub open spec fn inv(&self, memid: MemID) -> bool {
            &&& self.spec_memdb().inv(memid)
            &&& self.inv_regdb_any_cpu(memid)
            &&& self.spec_entities()[memid].dom().contains(self.spec_cpu())
        }
    }

    impl Archx64Op {
        pub open spec fn reg_write_requires(regname: &RegName, val: &RegValType) -> bool {
            match regname {
                RegName::Cpl => {false},
                RegName::Cr3 => {false},
                _ => {true}
            }
        }

        pub open spec fn op_requires(&self, sm_memid: MemID, arch: &Archx64) -> bool
        {
            self.to_memid().is_sm(sm_memid) ==>
            match self {
                Archx64Op::MemOp(memop, _) => {
                    arch.spec_memdb().vop_requires(*memop)
                },
                Archx64Op::RegWrite(_, reg_name, reg_val) => {
                    Self::reg_write_requires(reg_name, reg_val)
                },
                Archx64Op::RegRead(_, _) => {
                    true
                },
                Archx64Op::VMGExit(_) => {
                    true
                },
                Archx64Op::LoopHalt(_) => {
                    true
                },
            }
        }
    }
}

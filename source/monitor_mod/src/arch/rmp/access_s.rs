use super::*;
use crate::arch::rmp::perm_s::*;
use crate::*;

verus! {
    impl RmpEntry {
        pub open spec fn new(val: HiddenRmpEntryForPSP) -> Self {
            arbitrary::<RmpEntry>().spec_set_val(val)
        }
        #[verifier(opaque)]
        //memid, enc, gpmem, perm
        pub open spec fn check_access(&self, memid: MemID, enc: bool, gpmem: GPMem, perm: Perm) -> ResultOrErr<Self, MemError<()>>
        {
            if enc && !self@.check_gpn(gpmem.to_page()) {
                    ResultOrErr::Error(MemError::NestedPF(()))
            } else {
                self.check_access_no_addr_check(memid, enc, perm)
            }
        }

        pub open spec fn check_access_no_addr_check(&self, memid: MemID, enc: bool, perm: Perm) -> ResultOrErr<Self, MemError<()>>
        {
            if enc {
                if !self@.check_guest_reverse_mut_size_no_gpn(memid.to_asid(), PageSize::Size4k) {
                    ResultOrErr::Error(MemError::NestedPF(()))
                } else if !self@.check_validated() {
                    ResultOrErr::Error(MemError::NotValidated(()))
                } else if !self@.check_vmpl(memid.to_vmpl(), perm) {
                    ResultOrErr::Error(MemError::NestedPF(()))
                } else {
                    ResultOrErr::Ok(*self)
                }
            } else {
                if !self@.check_hypervisor_owned() {
                    ResultOrErr::Error(MemError::NestedPF(()))
                } else {
                    ResultOrErr::Ok(*self)
                }
            }
        }

        pub open spec fn trans(&self, op: RmpOp<SysPhy>) -> ResultWithErr<RmpEntry, MemError<RmpOp<SysPhy>>> {
            let ret = match op {
                RmpOp::RmpUpdate(_, newentry) => {
                    self.rmpupdate(newentry)
                }
                RmpOp::RmpAdjust(PageID{page, memid}, RmpAdjustParam{gpn, psize, vmsa, vmpl, perms}) => {
                    self.rmpadjust(memid, vmpl, psize, gpn, vmsa, perms)
                }
                RmpOp::Pvalidate(PageID{page, memid}, PvalidateParam{gpn, psize, val}) => {
                    self.pvalidate(memid, psize, gpn, val)
                }
            };
            let err = ret.to_err().with_param(op);
            ret.replace_err(err)
        }

        /// rmpupdate: only accept new asid gpa size assign immu;
        /// PSP will reset other fields automatically
        pub open spec fn _rmpupdate(&self, entry: RmpEntry) -> ResultWithErr<RmpEntry, MemError<()>> {
            let new = entry.view();
            if new.spec_size().is_Size2m() {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else if !new.spec_assigned() && (new.spec_immutable() || new.spec_asid() !== ASID_FOR_HV!()) {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else if self@.spec_immutable() {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else if !self@.spec_assigned() {
                let hidden = HiddenRmpEntryForPSP {
                    immutable: false,
                    assigned: false,
                    validated: false, vmsa: false,
                    asid: 0,
                    gpn: GPN::new(0),
                    size: PageSize::Size4k,
                    perms: rmp_perm_init(),
                };
                ResultWithErr::Ok(self.spec_set_val(hidden))
            } else {
                let reset = new.spec_asid() != self@.spec_asid() ||
                    new.spec_gpn() != self@.spec_gpn() ||
                    new.spec_size() != self@.spec_size() ||
                    new.spec_assigned() != self@.spec_assigned() ||
                    new.spec_asid() == 0;
                let hidden = HiddenRmpEntryForPSP {
                    immutable: new.spec_immutable(),
                    assigned: new.spec_assigned(),
                    validated: if reset{false} else {self@.validated},
                    vmsa: if reset{false} else {self@.vmsa},
                    asid: new.spec_asid(),
                    gpn: new.spec_gpn(),
                    size: new.spec_size(),
                    perms: if reset {rmp_perm_init()} else {self@.perms},
                };
                ResultWithErr::Ok(self.spec_set_val(hidden))
            }
            
        }

        pub open spec fn rmpupdate(&self, entry: RmpEntry) -> ResultWithErr<RmpEntry, MemError<()>> {
            let new = if !entry.view().spec_assigned()  || (entry.view().spec_asid() !== ASID_FOR_HV!()) {
                let newhidden = entry.view();
                let hidden = HiddenRmpEntryForPSP {
                    immutable: newhidden.spec_immutable(),
                    assigned: newhidden.spec_assigned(),
                    validated: false, vmsa: false,
                    asid: newhidden.spec_asid(),
                    gpn: newhidden.spec_gpn(),
                    size: newhidden.spec_size(),
                    perms: rmp_perm_init()
                };
                self.spec_set_val(hidden)
            } else {
                *self
            };

            if self@.spec_immutable() {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else {
                ResultWithErr::Ok(new)
            }
        }

        /// rmpadjust: only adjust vmsa and perm
        /// final step of the actual instruction;
        /// condition check happens in memory model
        pub open spec fn rmpadjust(&self, memid: MemID, vmpl: VMPL, psize: PageSize, gpn: GPN, vmsa: bool, perms: PagePerm) -> ResultWithErr<RmpEntry, MemError<()>>
            recommends
                memid.to_asid() == self.view().spec_asid(),
                memid.is_Guest(),
        {
            if vmpl.as_int() <= memid.to_vmpl().as_int() {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else if self.view().fault_rmp_update(memid.to_asid(), gpn, psize) {
                ResultWithErr::Error(*self, MemError::NestedPF(()))
            } else if !self.view().spec_validated(){
                ResultWithErr::Error(*self, MemError::NotValidated(()))
            } else if self.view().spec_size() == PageSize::Size4k && psize == PageSize::Size2m {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Size, ()))
            } else {
                let cur_perm = self.view().spec_perm(memid.to_vmpl());
                if !perms.subset_of(cur_perm)
                {
                    ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
                } else {
                    let hidden = self.view().spec_set_perm(vmpl, perms).spec_set_vmsa(vmsa);
                    ResultWithErr::Ok(self.spec_set_val(hidden))
                }
            }
        }

        /// pvalidate: change validate state
        /// final step of the actual instruction;
        /// input validation without rmp entry happens in MemDB::op_pvalidate
        pub open spec fn pvalidate(&self, memid: MemID, psize: PageSize, gpn: GPN, val: bool) -> ResultWithErr<RmpEntry, MemError<()>>
        {
            if !memid.to_vmpl().is_VMPL0() {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Perm, ()))
            } else if self.view().fault_rmp_update(memid.to_asid(), gpn, psize) {
                ResultWithErr::Error(*self, MemError::NestedPF(()))
            } else if self.view().spec_size() == PageSize::Size4k && psize == PageSize::Size2m {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::Size, ()))
            } else if self.view().spec_validated() === val {
                ResultWithErr::Error(*self, MemError::RmpOp(RmpFault::DoubleVal, ()))
            } else {
                let hidden = self.view().spec_set_validated(val);
                ResultWithErr::Ok(self.spec_set_val(hidden))
            }
        }
    }
}

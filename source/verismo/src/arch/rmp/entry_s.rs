use super::perm_s::{PagePerm, RmpPerm, *};
use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;

verus! {

impl HiddenRmpEntryForPSP {
    pub open spec fn inv_hvupdate_rel(self, preventry: Self) -> bool {
        &&& self.is_valid()
        &&& !preventry.validated
            ==> !self.validated
        //&&& self.validated ==> (self.perms === preventry.perms && self.asid === preventry.asid && preventry.validated && self.vmsa == preventry.vmsa && self.size == preventry.size)
        //&&& (self !== preventry)  ==> ((self.perms === super::perm_s::rmp_perm_init()))
        &&& (self !== preventry) ==> {
            &&& self.perms[VMPL::VMPL0] =~~= PagePerm::full()
            &&& self.perms[VMPL::VMPL0] =~~= preventry.perms[VMPL::VMPL0]
            &&& self.perms[VMPL::VMPL1].subset_of(preventry.perms[VMPL::VMPL1])
            &&& self.perms[VMPL::VMPL2].subset_of(preventry.perms[VMPL::VMPL2])
            &&& self.perms[VMPL::VMPL3].subset_of(preventry.perms[VMPL::VMPL3])
            &&& (self.perms[VMPL::VMPL1] === PagePerm::empty() || self.perms[VMPL::VMPL1]
                === preventry.perms[VMPL::VMPL1])
            &&& (self.perms[VMPL::VMPL2] === PagePerm::empty() || self.perms[VMPL::VMPL2]
                === preventry.perms[VMPL::VMPL2])
            &&& (self.perms[VMPL::VMPL3] === PagePerm::empty() || self.perms[VMPL::VMPL3]
                === preventry.perms[VMPL::VMPL3])
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_set_perm(&self, vmpl: VMPL, perm: PagePerm) -> Self {
        self.spec_set_perms(self.spec_perms().insert(vmpl, perm))
    }

    #[verifier(inline)]
    pub open spec fn spec_perm(&self, vmpl: VMPL) -> PagePerm {
        self.spec_perms().index(vmpl)
    }

    // is private to vmpl-x and vmpl-0
    pub open spec fn is_vmpl_private(&self, vmpl: int) -> bool {
        &&& self.spec_validated()
        &&& vmpl != VMPL::VMPL1.as_int() ==> !self.spec_perms()[VMPL::VMPL1].contains(Perm::Write)
        &&& vmpl != VMPL::VMPL2.as_int() ==> !self.spec_perms()[VMPL::VMPL2].contains(Perm::Write)
        &&& vmpl != VMPL::VMPL3.as_int() ==> !self.spec_perms()[VMPL::VMPL3].contains(Perm::Write)
    }

    pub open spec fn is_confidential_to(&self, vmpl: int) -> bool
        recommends
            0 < vmpl <= 4,
    {
        if vmpl >= 4 {
            self.spec_validated()
        } else {
            &&& self.spec_validated()
            &&& self.spec_perms()[VMPL::spec_from_int(vmpl).get_Some_0()] =~= PagePerm::empty()
        }
    }

    pub open spec fn is_init_for_asid(&self, asid: int) -> bool {
        // Do not allow asid reuse;
        self.spec_asid() != asid ||
        // Before VM's operatioin
        (self.spec_asid() == asid && rmp_perm_is_init(self.perms))
    }

    pub open spec fn is_valid(&self) -> bool {
        &&& (self.spec_asid() != 0 || !self.spec_assigned())
        &&& (!self.spec_validated() || (self.spec_assigned() && self.spec_asid() != 0))
        &&& self.perms[VMPL::VMPL0]
            === Set::full()
        //&&& !self.validated ==> self.perms === super::perm_s::rmp_perm_init() Not Hold

    }

    pub open spec fn fault_rmp_update(&self, asid: ASID, gpn: GPN, size: PageSize) -> bool {
        ||| self.spec_immutable()
        ||| !self.spec_assigned()
        ||| self.spec_gpn() !== gpn
        ||| self.spec_asid() !== asid
        ||| (self.spec_size() == PageSize::Size2m && size == PageSize::Size4k)
        ||| !self.is_valid()
    }

    pub open spec fn okay_with_pvalidate(
        &self,
        asid: ASID,
        gpn: GPN,
        size: PageSize,
        validated: bool,
    ) -> bool {
        &&& self.spec_immutable() == false
        &&& self.spec_assigned() == true
        &&& self.spec_asid() == asid
        &&& self.spec_gpn() === gpn
        &&& self.spec_size() == size
        &&& self.spec_validated() == (!validated)
    }

    pub open spec fn check_hypervisor_owned(&self) -> bool {
        !self.spec_assigned()
    }

    pub open spec fn check_guest_reverse_mut_size_no_gpn(
        &self,
        asid: ASID,
        size: PageSize,
    ) -> bool {
        &&& self.spec_immutable() == false
        &&& self.spec_assigned() == true
        &&& self.spec_asid() == asid
        &&& self.spec_size() == size
    }

    pub open spec fn check_gpn(&self, gpn: GPN) -> bool {
        self.spec_gpn() === gpn
    }

    pub open spec fn check_guest_reverse_mut_size(
        &self,
        asid: ASID,
        gpn: GPN,
        size: PageSize,
    ) -> bool {
        &&& self.check_gpn(gpn)
        &&& self.check_guest_reverse_mut_size_no_gpn(asid, size)
    }

    pub open spec fn check_validated(&self) -> bool {
        self.spec_validated()
    }

    #[verifier(inline)]
    pub open spec fn check_vmpl(&self, vmpl: VMPL, p: super::perm_s::Perm) -> bool {
        self.spec_perm(vmpl).contains(p)
    }
}

} // verus!

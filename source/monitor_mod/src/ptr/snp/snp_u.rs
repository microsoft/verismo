use super::*;
use crate::arch::entities::*;
use crate::arch::errors::MemError;
use crate::arch::memop::*;
use crate::arch::reg::*;
use crate::arch::rmp::perm_s::*;
use crate::arch::rmp::*;
use crate::arch::x64::*;
use crate::registers::SnpCore;

verus! {

#[repr(C, align(1))]
#[vbit_struct(RmpAttr, u64)]
pub struct RmpAttrSpec {
    #[vbits(0, 7)]
    pub vmpl: u64,
    #[vbits(8, 15)]
    pub perms: u64,
    #[vbits(16, 16)]
    pub vmsa: u64,
}

#[derive(SpecSetter, SpecGetter)]
pub ghost struct PTAttr {
    pub encrypted: bool,
    pub w: bool,
    pub x: bool,
}

impl PTAttr {
    pub open spec fn code() -> Self {
        PTAttr { encrypted: true, w: false, x: true }
    }
}

impl SpecDefault for PTAttr {
    open spec fn spec_default() -> Self {
        PTAttr { encrypted: true, w: true, x: false }
    }
}

// software tracked memory attr
#[derive(SpecSetter, SpecGetter)]
pub ghost struct SwSnpMemAttr {
    // RMP related
    pub rmp: RmpEntry,
    // PTE related
    pub guestmap: Map<int, int>,
    pub sysmap: Map<int, int>,  // unused in SW state
    pub rmpmap: Map<int, int>,  // SPA -> GPA
    // When there are more than one pte in the queue,
    // we do not guarantee the actual pte used by the perm token.
    pub pte: Seq<PTAttr>,
    pub is_pte: bool,
}

pub type HwSnpMemAttr = SwSnpMemAttr;

impl RmpAttrSpec {
    pub open spec fn perms(&self) -> PagePerm {
        PagePerm::from_int(self.spec_perms() as int)
    }

    pub open spec fn is_vmsa(&self) -> bool {
        self.spec_vmsa() == 1
    }

    pub open spec fn vmpl(&self) -> VMPL
        recommends
            self.valid_vmpl(),
    {
        VMPL::from_int(self.spec_vmpl() as int)
    }

    pub open spec fn valid_vmpl(&self) -> bool {
        VMPL::spec_from_int(self.spec_vmpl() as int).is_Some()
    }

    pub open spec fn from(vmpl: VMPL, vmsa: bool, perms: u8) -> Self {
        RmpAttrSpec::empty().spec_set_vmpl(vmpl.as_int() as u64).spec_set_vmsa(
            if vmsa {
                1
            } else {
                0
            },
        ).spec_set_perms(perms as u64)
    }
}

impl RmpAttr {
    pub fn from(vmpl: VMPL, vmsa: bool, perms: u8) -> (ret: Self)
        ensures
            ret@ === RmpAttrSpec::from(vmpl, vmsa, perms),
            ret@.valid_vmpl(),
    {
        RmpAttr::empty().set_vmpl(vmpl.as_u64()).set_vmsa(
            if vmsa {
                1
            } else {
                0
            },
        ).set_perms(perms as u64)
    }
}

impl SwSnpMemAttr {
    pub spec fn pte(&self) -> PTAttr;

    #[verifier(broadcast_forall)]
    #[verifier(external_body)]
    pub proof fn axiom_pte(&self)
        ensures
            self.pte.len() == 1 ==> #[trigger] self.pte() === self.pte.last(),
    {
    }

    pub open spec fn encrypted(&self) -> bool {
        self.pte().encrypted
    }

    #[verifier(inline)]
    pub open spec fn deterministic_pte(&self) -> bool {
        &&& self.pte.len() == 1
        &&& self.pte() === self.pte.last()
        &&& self.guestmap =~~= Map::new(|gva: int| true, |gva: int| spec_va_to_pa(gva))
    }

    pub open spec fn is_vm_confidential(&self) -> bool {
        &&& self.encrypted()
        &&& self.rmp@.spec_validated()
    }

    pub open spec fn is_vmpl_private(&self, vmpl: int) -> bool {
        &&& self.is_vm_confidential()
        &&& self.rmp@.is_vmpl_private(vmpl)
    }

    pub open spec fn is_confidential_to(&self, vmpl: int) -> bool {
        &&& self.is_vm_confidential()
        &&& self.rmp@.is_confidential_to(vmpl)
    }

    pub open spec fn is_vmpl0_private(&self) -> bool {
        &&& self.is_vmpl_private(0)
    }

    #[verifier(inline)]
    pub open spec fn is_hv_shared(&self) -> bool {
        !self.is_confidential_to(4)
    }

    pub open spec fn is_vmpl0_confidential(&self) -> bool {
        &&& self.is_confidential_to(1)
        &&& self.is_confidential_to(2)
        &&& self.is_confidential_to(3)
        &&& self.is_confidential_to(4)
    }

    pub open spec fn inv_confidential(&self) -> bool {
        &&& self.is_confidential_to(4) ==> self.encrypted()
        &&& (self.is_confidential_to(1) || self.is_confidential_to(2) || self.is_confidential_to(3))
            ==> self.is_confidential_to(4)
    }

    pub open spec fn ensures_read<T: WellFormed + IsConstant>(
        self,
        val: Option<T>,
        ret: T,
    ) -> bool {
        &&& val.is_Some() && self.is_vmpl0_private() ==> { val === Some(ret) }
        &&& ret.wf()
        &&& !self.is_confidential_to(1) ==> ret.is_constant_to(1)
        &&& !self.is_confidential_to(2) ==> ret.is_constant_to(2)
        &&& !self.is_confidential_to(3) ==> ret.is_constant_to(3)
        &&& !self.is_confidential_to(4) ==> ret.is_constant_to(4)
    }
}

impl HwSnpMemAttr {
    pub open spec fn hvupdate_rel(self, prev: Self) -> bool {
        &&& self.rmp@.inv_hvupdate_rel(prev.rmp@)
        &&& self.pte == prev.pte  // proved by arch pgtable
        //&&& self.rmp@.validated ==> self.rmpmap === prev.rmpmap

    }

    pub proof fn proof_hvupdate_rel_propograte(next: Self, current: Self, prev: Self)
        requires
            next.hvupdate_rel(current),
            current.hvupdate_rel(prev),
        ensures
            next.hvupdate_rel(prev),
    {
    }
}

pub ghost struct SnpMemAttr {
    pub hw: HwSnpMemAttr,  // hardware rmp state
    pub sw: SwSnpMemAttr,
}

impl SnpMemAttr {
    pub proof fn proof_valid_access(self, vaddr: int, size: nat, p: Perm)
        requires
            p.is_Write() || p.is_Read(),
            self.valid_access(vaddr, size, p),
            self.wf(),
        ensures
            self.sw.is_vmpl0_private()
                ==> self.hw.is_vmpl0_private(),
    //self.hw.is_vmpl0_private() ==> self.sw.is_vmpl0_private(),

    {
        assert(self.hw.rmp@.inv_hvupdate_rel(self.sw.rmp@));
        if self.hw.is_vmpl0_private() {
            assert(self.sw.is_vm_confidential());
        }
    }
}

pub trait SnpMemAttrTrait {
    spec fn snp(&self) -> SwSnpMemAttr;

    spec fn hw_snp(&self) -> HwSnpMemAttr;
}

impl SnpMemAttrTrait for SnpMemAttr {
    open spec fn snp(&self) -> SwSnpMemAttr {
        self.sw
    }

    open spec fn hw_snp(&self) -> HwSnpMemAttr {
        self.hw
    }
}

impl SwSnpMemAttr {
    pub open spec fn wf(&self) -> bool {
        &&& self.rmp.inv()
        &&& self.inv_confidential()
        &&& self.deterministic_pte()
        &&& (*self === SwSnpMemAttr::spec_default().spec_set_rmp(self.rmp).spec_set_pte(self.pte))
        &&& self.rmp@.spec_asid() == SwSnpMemAttr::spec_default().rmp@.spec_asid()
        &&& self.rmp@.spec_gpn() == SwSnpMemAttr::spec_default().rmp@.spec_gpn()
        &&& self.rmp@.spec_size() == SwSnpMemAttr::spec_default().rmp@.spec_size()
        &&& !self.pte().spec_encrypted() ==> !self.rmp@.spec_validated()
    }

    pub open spec fn init() -> Self {
        let rmp_psp = HiddenRmpEntryForPSP {
            validated: false,
            vmsa: false,
            perms: crate::arch::rmp::perm_s::rmp_perm_init(),
            immutable: false,
            assigned: true,
            asid: arbitrary::<nat>() + 1,
            gpn: arbitrary(),  // unused
            size: PageSize::Size4k,  // unused
        };
        SwSnpMemAttr {
            rmp: arbitrary::<RmpEntry>().spec_set_val(rmp_psp),
            pte: seq![PTAttr::spec_default()],
            is_pte: false,
            guestmap: Map::new(|gva: int| true, |gva: int| gva),
            rmpmap: Map::empty(),
            sysmap: Map::empty(),
        }
    }

    pub open spec fn allocator_default() -> Self {
        let rmp_psp = HiddenRmpEntryForPSP {
            validated: true,
            vmsa: false,
            perms: crate::arch::rmp::perm_s::rmp_perm_init(),
            immutable: false,
            assigned: true,
            asid: arbitrary::<nat>() + 1,
            gpn: arbitrary(),  // unused
            size: PageSize::Size4k,  // unused
        };
        Self::init().spec_set_rmp(RmpEntry { val: rmp_psp })
    }

    pub open spec fn spec_default_pte() -> Self {
        Self::spec_default().spec_set_is_pte(true)
    }

    pub open spec fn executable() -> Self {
        Self::spec_default().spec_set_pte(seq![PTAttr::code()])
    }

    pub open spec fn shared() -> Self {
        let rmp_psp = HiddenRmpEntryForPSP {
            validated: false,
            vmsa: false,
            perms: crate::arch::rmp::perm_s::rmp_perm_init(),
            immutable: false,
            assigned: false,
            asid: ASID_FOR_HV!(),
            gpn: arbitrary(),  // unused
            size: PageSize::Size4k,  // unused
        };
        Self::spec_default().spec_set_rmp(
            arbitrary::<RmpEntry>().spec_set_val(rmp_psp),
        ).spec_set_pte(seq![PTAttr::spec_default().spec_set_encrypted(false)])
    }

    pub open spec fn vmsa() -> Self {
        let base = Self::spec_default();
        base.spec_set_rmp(RmpEntry { val: base.rmp.val.spec_set_vmsa(true) })
    }/*pub open spec fn vmsa2(attr: RmpAttrSpec) -> Self {
        let base  = Self::spec_default();
        let rmp = base.rmp.val;
        let rmpperms = rmp.perms.insert(attr.vmpl(), attr.perms());
        base.spec_set_rmp(
            RmpEntry {
                val: rmp.spec_set_perms(rmpperms).spec_set_vmsa(true)
            }
        )
    }*/

}

impl SpecDefault for SwSnpMemAttr {
    open spec fn spec_default() -> Self {
        SwSnpMemAttr::allocator_default()
    }
}

impl SwSnpMemAttr {
    #[verifier(inline)]
    pub open spec fn is_default(&self) -> bool {
        &&& *self === SwSnpMemAttr::spec_default()
    }

    pub open spec fn is_shared_from(&self, old: Self) -> bool {
        &&& self.is_shared()
        &&& self.rmp@.gpn === old.rmp@.gpn
        &&& old.pte().spec_set_encrypted(false) === self.pte()
    }

    #[verifier(inline)]
    pub open spec fn is_shared(&self) -> bool {
        &&& self.rmp@ === SwSnpMemAttr::shared().rmp@.spec_set_gpn(self.rmp@.gpn)
        &&& !self.pte().spec_encrypted()
    }
}

// Partial Eq on software parts
impl VSpecEq<SnpMemAttr> for SnpMemAttr {
    #[verifier(inline)]
    open spec fn spec_eq(self, rhs: Self) -> bool {
        &&& self.sw_eq(rhs)
    }
}

impl SnpMemAttr {
    #[verifier(inline)]
    pub open spec fn sw_eq(self, rhs: Self) -> bool {
        &&& self.sw === rhs.sw
    }

    #[verifier(inline)]
    pub open spec fn sw_default(&self) -> bool {
        &&& self.sw === SwSnpMemAttr::spec_default()
    }

    pub closed spec fn map_wf(&self) -> bool {
        &&& self.hw.guestmap === self.sw.guestmap
    }

    pub open spec fn hw_rmp_wf(&self) -> bool {
        // software-hardware relationship
        &&& self.hw.hvupdate_rel(self.sw)
        &&& self.hw.rmp.inv()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.hw_rmp_wf()
        // rmp status is valid

        &&& self.snp().wf()
        // vmpl-x secret must be stored in vmpl-x's confidential memory.

    }
}

} // verus!

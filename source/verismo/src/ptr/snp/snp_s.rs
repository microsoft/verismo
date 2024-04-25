use super::*;
use crate::arch::entities::*;
use crate::arch::errors::MemError;
use crate::arch::memop::*;
use crate::arch::reg::*;
use crate::arch::rmp::perm_s::*;
use crate::arch::rmp::*;
use crate::arch::x64::*;
use crate::registers::{CoreIdPerm, SnpCore};
use crate::snp::cpu::VmsaPage;

verus! {

impl SwSnpMemAttr {
    pub open spec fn ensures_rmpupdate(&self, prev: Self, shared: bool, page_2m: bool) -> bool {
        let rmp = prev.rmp@;
        let asid = if shared {
            ASID_FOR_HV!()
        } else {
            rmp.spec_asid()
        };
        let hidden = HiddenRmpEntryForPSP {
            immutable: rmp.spec_immutable(),
            assigned: !shared,
            validated: false,
            vmsa: false,
            asid,
            gpn: rmp.spec_gpn(),
            size: if page_2m {
                PageSize::Size2m
            } else {
                PageSize::Size4k
            },
            perms: rmp_perm_init(),
        };
        let newrmp = RmpEntry { val: hidden };
        &&& prev.rmp.rmpupdate(newrmp).is_Ok()
        &&& self.rmp === prev.rmp.rmpupdate(newrmp).get_Ok_0()
        &&& *self === prev.spec_set_rmp(self.rmp)
    }

    pub open spec fn requires_pvalidate(&self, vaddr: int, is_2m: int, val: int) -> bool {
        &&& is_2m % 2 == 0  // Only support 4k page

        &&& (val % 2 == 0)
            == self.rmp@.spec_validated()
        //&&& (val % 2 == 1) ==>  self.rmp@.perms =~~= rmp_perm_init()

        &&& self.deterministic_pte()
        &&& self.encrypted()
    }

    pub open spec fn ensures_pvalidated(&self, prev: Self, val: bool) -> bool {
        &&& self.rmp@ === prev.rmp@.spec_set_validated(val)
        &&& *self === prev.spec_set_rmp(self.rmp)
    }

    // VMSA vmpl is determined only by vmpl field in vmsa page
    // attr.vmpl only decide which vmpl the permission assigned to.
    // attr.vmpl must be higher than the current vmpl
    pub open spec fn requires_rmpadjust(
        &self,
        vaddr: int,
        is_2m: int,
        attr: RmpAttrSpec,
        newcore: Option<CoreIdPerm>,
        memperm: SnpPointsToBytes,
    ) -> bool {
        let vmsa: VmsaPage = memperm.bytes().vspec_cast_to();
        let vmpl = vmsa.vmpl;
        &&& self.requires_rmpadjust_mem(vaddr, is_2m, attr, newcore)
        &&& attr.is_vmsa() ==> vmpl.spec_eq(newcore.get_Some_0()@.vmpl)
    }

    pub open spec fn requires_rmpadjust_mem(
        &self,
        vaddr: int,
        is_2m: int,
        attr: RmpAttrSpec,
        newcore: Option<CoreIdPerm>,
    ) -> bool {
        &&& is_2m % 2 == 0  // Only support 4k page

        &&& 1 <= attr.spec_vmpl() <= 3
        &&& attr.is_vmsa() ==> newcore.is_Some()
        &&& !attr.is_vmsa() ==> newcore.is_None()
        &&& self.rmp@.spec_validated()  // need to be validated before rmpadjust, otherwises it will never return.
        &&& self.wf()
    }

    pub open spec fn ensures_rmpadjust(&self, prev: Self, attr: RmpAttrSpec) -> bool {
        &&& self.rmp@ === prev.rmp@.spec_set_perms(
            prev.rmp@.perms.insert(attr.vmpl(), attr.perms()),
        ).spec_set_vmsa(attr.is_vmsa())
        &&& *self === prev.spec_set_rmp(self.rmp)
    }
}

impl HwSnpMemAttr {
    // True -> Return
    // False -> Never return
    pub open spec fn valid_memmap(self, start: int, size: nat) -> bool {
        forall|vaddr|
            start <= vaddr < start + size ==> self.guestmap[vaddr]
                == self.rmpmap[self.sysmap[self.guestmap[vaddr]]]
    }

    // True -> Return
    // False -> Never return
    pub open spec fn valid_access(self, vmid: nat, vaddr: int, size: nat, perm: Perm) -> bool
        recommends
            vmid >= 1,
    {
        let memid = MemID::Guest((vmid - 1) as nat, VMPL::VMPL0);
        &&& self.rmp.check_access_no_addr_check(memid, self.encrypted(), perm).is_Ok()
        &&& self.encrypted() ==> self.valid_memmap(vaddr, size)
    }

    // True -> Return
    // False -> Never return
    pub open spec fn rmpadjust_ret(
        self,
        new: Self,
        rax: u64,
        vmid: nat,
        vaddr: int,
        psize: PageSize,
        vmpl: VMPL,
        is_vmsa: bool,
        perms: PagePerm,
    ) -> bool
        recommends
            vmid > 0,
    {
        let memid = MemID::Guest((vmid - 1) as nat, VMPL::VMPL0);
        let ret = self.rmp.rmpadjust(
            memid,
            vmpl,
            psize,
            GPA::new(self.guestmap[vaddr]).to_page(),
            is_vmsa,
            perms,
        );
        let size = (if psize.is_Size4k() {
            PAGE_SIZE!()
        } else {
            0x2000_000
        }) as nat;
        let map_ok = new.valid_memmap(vaddr, size);
        if map_ok {
            if let ResultWithErr::Error(_, memerr) = ret {
                let arch: Archx64 = arbitrary();
                let memop: MemOp<GuestVir> = choose|memop: MemOp<GuestVir>|
                    memop.is_RmpOp() && memop.get_RmpOp_0().is_RmpAdjust();
                let op = choose|op: Archx64Op|
                    op.to_memid() === memid && op.is_MemOp() && op.get_MemOp_0() === memop;
                let (trap, trans) = Archx64::handle_mem_err_fn(MemError::from_err(memerr, memop));
                if !trap {
                    &&& rax == trans(arch, op).spec_regdb()[op.cpu_memid()].spec_index(RegName::Rax)
                    &&& new === self
                    &&& arch.is_run(op.cpu_memid())
                } else {
                    false
                }
            } else {
                new === self.spec_set_rmp(ret.to_result())
            }
        } else {
            false
        }
    }

    // True -> Return
    // False -> Never return
    pub open spec fn pvalidate_ret(
        self,
        new: Self,
        rax: u64,
        rflags: u64,
        vmid: nat,
        vaddr: int,
        psize: PageSize,
        val: bool,
    ) -> bool
        recommends
            vmid > 0,
    {
        let memid = MemID::Guest((vmid - 1) as nat, VMPL::VMPL0);
        let page = GVA::new(vaddr).to_page();
        let ret = self.rmp.pvalidate(memid, psize, self.rmp@.gpn, val);
        let size = if psize.is_Size4k() {
            PAGE_SIZE!()
        } else {
            0x2000_000
        };
        let map_ok = self.valid_memmap(vaddr, size as nat);
        if map_ok {
            if let ResultWithErr::Error(_, memerr) = ret {
                let arch: Archx64 = arbitrary();
                let memop: MemOp<GuestVir> = choose|memop: MemOp<GuestVir>|
                    memop.is_RmpOp() && memop.get_RmpOp_0().is_Pvalidate();
                let op = choose|op: Archx64Op|
                    op.to_memid() === memid && op.is_MemOp() && op.get_MemOp_0() === memop;
                let (trap, trans) = Archx64::handle_mem_err_fn(MemError::from_err(memerr, memop));
                if !trap {
                    &&& rax == trans(arch, op).spec_regdb()[op.cpu_memid()].spec_index(RegName::Rax)
                    &&& rflags == trans(arch, op).spec_regdb()[op.cpu_memid()].spec_index(
                        RegName::Rflags,
                    )
                    &&& self === new
                    &&& arch.is_run(op.cpu_memid())
                } else {
                    false
                }
            } else {
                new === self.spec_set_rmp(ret.to_result())
            }
        } else {
            false
        }
    }

    pub proof fn reveal_use_rflags()
        ensures
            forall|rflags: u64| bits_p::spec_bit_set(rflags, RflagBit::CF.as_int() as u64) != 0,
    {
        assert forall|rflags: u64|
            bits_p::spec_bit_set(rflags, RflagBit::CF.as_int() as u64) != 0 by {
            let b = RflagBit::CF.as_int() as u64;
            bit_set_non_zero(rflags, b);
        }
    }
}

impl SnpMemAttr {
    pub open spec fn valid_access(self, vaddr: int, size: nat, perm: Perm) -> bool {
        &&& self.hw.valid_access(self.sw.rmp@.asid, vaddr, size, perm)
    }

    pub open spec fn pvalidate_ret(
        self,
        new: Self,
        rax: u64,
        rflags: u64,
        vaddr: int,
        is_2m: int,
        val: int,
    ) -> bool {
        let psize = if is_2m % 2 == 0 {
            PageSize::Size4k
        } else {
            PageSize::Size4k
        };
        let validated = val % 2 == 1;
        &&& self.hw.pvalidate_ret(new.hw, rax, rflags, self.sw.rmp@.asid, vaddr, psize, validated)
        &&& if (rax == 0 && !spec_has_bit_set(rflags, RflagBit::CF.as_int() as u64)) {
            &&& new.sw.ensures_pvalidated(self.sw, validated)
        } else {
            new.sw === self.sw
        }
    }

    /*pub proof fn proof_pvalidate_ret_wf(self, new: Self, rax: u64, rflags: u64, vaddr: int, is_2m: int, val: int)
        requires
            self.wf(),
            self.pvalidate_ret(new, rax, rflags, vaddr, is_2m, val)
        ensures
            (rax == 0 && !bits_p::spec_has_bit_set(rflags, RflagBit::CF.as_int() as u64)) ==> new.rmp_wf()
        {
            let memid = MemID::Guest((self.sw.rmp@.asid - 1) as nat, VMPL::VMPL0);
            assert forall |rflags: u64| bits_p::spec_bit_set(rflags, RflagBit::CF.as_int() as u64) != 0 by
            {
                let b =  RflagBit::CF.as_int() as u64;
                bit_set_non_zero(rflags, b);
            }
            if (rax == 0 && bits_p::spec_bit_set(rflags, RflagBit::CF.as_int() as u64) == 0) {
                let psize = if is_2m % 2 == 0 {PageSize::Size4k} else {PageSize::Size4k};
                let validated = val % 2 == 1;
                assert(new.hw.rmp === self.hw.rmp.pvalidate(memid, psize, self.hw.rmp@.gpn, validated).to_result());
                assert(self.hw.rmp.pvalidate(memid, psize, self.hw.rmp@.gpn, validated).is_Ok());
                assert(new.hw.rmp !== self.hw.rmp);
                assert(self.hw.hvupdate_rel(self.sw));
                assert(new.hw.rmp@.is_valid());
                assert(new.hw.rmp@.spec_validated() == validated);
                assert(new.sw.rmp@.spec_validated() == validated);
                assert(new.hw.hvupdate_rel(new.sw));
                assert(new.sw.pte() === new.sw.pte.last());
            }
        }*/
    pub open spec fn rmpadjust_ret(
        self,
        new: Self,
        rax: u64,
        vaddr: int,
        is_2m: int,
        attr: RmpAttrSpec,
    ) -> bool {
        let psize = if is_2m % 2 == 0 {
            PageSize::Size4k
        } else {
            PageSize::Size4k
        };
        &&& self.hw.rmpadjust_ret(
            new.hw,
            rax,
            self.sw.rmp@.asid,
            vaddr,
            psize,
            attr.vmpl(),
            attr.is_vmsa(),
            attr.perms(),
        )
        &&& if (rax == 0) {
            new.sw.ensures_rmpadjust(self.sw, attr)
        } else {
            new.sw === self.sw
        }
    }
}

} // verus!

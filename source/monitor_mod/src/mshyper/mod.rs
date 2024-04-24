mod hypercall;
mod wakeup;

use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::entities::VMPL;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::pgtable_e::va_to_pa;
use crate::ptr::*;
use crate::registers::*;
use crate::snp::cpu::VmsaPage;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::vbox::*;
use crate::*;

verus! {

pub type HvCallStatus = u64;

pub const HV_STATUS_TIMEOUT: u64 = 0x78u64;

pub const HV_MAX_RETRY: usize = 10;

// Hypercalls
pub const HVCALL_SET_VP_REGISTERS: u32 = 0x0051;

pub const HVCALL_GET_VP_REGISTERS: u32 = 0x0050;

pub const HVCALL_ENABLE_VP_VTL: u32 = 0x000f;

pub const HVCALL_START_VIRTUAL_PROCESSOR: u32 = 0x0099;

// Hyper-V registers
pub const HV_REGISTER_VSM_PARTITION_CONFIG: u32 = 0x000d0007;

/* SEV control register */

pub const HV_X64_REGISTER_SEV_CONTROL: u32 = 0x00090040;

pub const HV_X64_REGISTER_SEV_CONTROL_USE_SEV: u64 = 0x1;

/* MSR used to identify the guest OS. */

pub const SECURITY_MONITOR_GUEST_ID: u64 = 0x123;

// Any non-zero values work
pub const HV_X64_MSR_GUEST_OS_ID: u32 = 0x40000000;

/* intercept MSR */

pub const HV_X64_MSR_SINT0: u32 = 0x40000090;

pub const KeX64VectorSintIntercept: u64 = 0x30;

pub const HV_REGISTER_GUEST_VSM_PARTITION_CONFIG: u32 = 0x000D0008;

pub const HV_PARTITION_ID_SELF: u64 = 0xffff_ffff_ffff_ffffu64;

pub const HV_VP_INDEX_SELF: u32 = 0xffff_fffeu32;

pub const REG_NO_USE_VTL: u8 = 0;

pub const REG_USE_VTL: u8 = 0x10;

pub type HyperPageHandle = VBox<OnePage>;

pub struct GhcbHyperPageHandle(pub GhcbHandle, pub HyperPageHandle);

} // verus!
verus! {

pub closed spec fn spec_vtl_vmpl_map(vtl: int, vmpl: u8) -> bool {
    ||| (vtl == 2 && vmpl == 0)
    ||| (vtl == 0 && vmpl != 0)
}

pub fn get_vtl(vmpl: u8) -> (vtl: u8)
    ensures
        spec_vtl_vmpl_map(vtl as int, vmpl),
{
    if vmpl == 0 {
        2
    } else {
        0
    }
}

pub closed spec fn _hyperpage_wf(id: int, snp: SwSnpMemAttr) -> bool {
    &&& snp === SwSnpMemAttr::shared()
    &&& id % PAGE_SIZE!() == 0
}

impl VBox<OnePage> {
    pub open spec fn hyperpage_wf(&self) -> bool {
        &&& self@.is_constant()
        &&& _hyperpage_wf(self.id(), self.snp())
    }
}

// Register OD ID and mark hyperpage as shared.
pub fn hyperv_register(
    handle: GhcbHyperPageHandle,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (handles: GhcbHyperPageHandle)
    requires
        handle.wf(),
        old(cs).inv(),
    ensures
        handles.wf(),
        cs.inv(),
        cs.only_lock_reg_coremode_updated(
            *old(cs),
            set![GHCB_REGID()],
            set![spec_PT().lockid(), spec_CONSOLE().lockid()],
        ),
{
    let GhcbHyperPageHandle(ghcb_handle, hyperpage_handle) = handle;
    let ghost cs1 = *cs;
    let ghcb_handle = ghcb_handle.ghcb_write_msr(
        HV_X64_MSR_GUEST_OS_ID,
        SECURITY_MONITOR_GUEST_ID,
        Tracked(cs),
    );
    let ghost cs2 = *cs;
    let (read, ghcb_handle) = ghcb_handle.ghcb_read_msr(HV_X64_MSR_GUEST_OS_ID, Tracked(cs));
    let ghost cs3 = *cs;
    proof {
        cs1.lemma_update_prop(cs2, *cs, set![], set![spec_PT().lockid()], set![], set![]);
        assert(set![spec_PT().lockid()].union(set![]) =~~= set![spec_PT().lockid()]);
        reveal_strlit("Register OS ID: ");
    }
    (new_strlit("Register OS ID: "), read).debug(Tracked(cs));
    proof {
        cs1.lemma_update_prop(
            cs3,
            *cs,
            set![],
            set![spec_PT().lockid()],
            set![GHCB_REGID()],
            set![spec_CONSOLE().lockid()],
        );
        assert(set![spec_PT().lockid()].union(set![spec_CONSOLE().lockid()])
            =~~= set![spec_PT().lockid(), spec_CONSOLE().lockid()]);
        assert(set![].union(set![GHCB_REGID()]) =~~= set![GHCB_REGID()]);
    }
    GhcbHyperPageHandle(ghcb_handle, hyperpage_handle)
}

} // verus!
verismo_simple! {
#[repr(C, packed)]
pub struct RegSetEntry {
    pub name: u32,
    pub reserved_2: u32,
    pub reserved_3: u64,
    pub value_low: u64,
    pub value_high: u64,
}

#[repr(C, packed)]
pub struct HvCallInputSetReg {
    pub ptid: u64,
    pub vpid: u32,
    pub vtl: u8,
    pub reserved: [u8; 3],
    pub element: RegSetEntry,
}

#[repr(C, packed)]
pub struct RegGetEntry {
    pub name0: u32,
    pub name1: u32,
}

#[repr(C, packed)]
pub struct HvCallInputGetReg {
    pub ptid: u64,
    pub vpid: u32,
    pub vtl: u8,
    pub reserved: [u8; 3],
    pub element: RegGetEntry,
}

#[repr(C, packed)]
#[derive(Copy, VClone)]
pub struct HvCallOutputGetReg {
    pub low: u64,
    //pub high: u64,
}

use crate::debug::VPrint;
#[repr(C, align(1))]
#[derive(VPrint)]
pub struct HvCallVpVtlInput {
    pub ptid: u64,
    pub vpid: u32,
    pub vtl: u32,
    pub vmsa_addr: u64,
    pub reserved_ctx: [u64; 27],
}
}

verus! {

impl HvCallVpVtlInput {
    pub fn new(ptid: u64, vpid: u32, vtl: u8, vmsa_addr: u64) -> (ret: Self)
        ensures
            ret.ptid.spec_eq(ptid),
            ret.vpid.spec_eq(vpid),
            ret.vtl.spec_eq(vtl),
            ret.vmsa_addr.spec_eq((vmsa_addr | HV_X64_REGISTER_SEV_CONTROL_USE_SEV)),
            ret.is_constant(),
    {
        let vmsa_addr = vmsa_addr | HV_X64_REGISTER_SEV_CONTROL_USE_SEV;
        HvCallVpVtlInput {
            ptid: ptid.into(),
            vpid: vpid.into(),
            vtl: vtl.into(),
            vmsa_addr: vmsa_addr.into(),
            reserved_ctx: Array::new(u64_s::new(0)),
        }
    }
}

} // verus!
verus! {

#[inline]
pub fn hvcall_code(lower: u32, upper: u32) -> (ret: u64)
    ensures
        ret == add(lower as u64, (upper as u64) << 32u64),
{
    let ghost upper64 = upper as u64;
    assert((upper64 << 32u64) <= 0xffff_ffff_0000_0000) by (bit_vector)
        requires
            upper64 == upper as u64,
    ;
    ((upper as u64) << 32u64) + (lower as u64)
}

impl GhcbHyperPageHandle {
    pub open spec fn wf(&self) -> bool {
        &&& self.0.ghcb_wf()
        &&& self.1.hyperpage_wf()
    }
}

} // verus!

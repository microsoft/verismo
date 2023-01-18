use registers::*;

use super::*;
use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::reg::*;
use crate::debug::VPrint;
use crate::global::spec_ALLOCATOR_lockid;
use crate::ptr::*;
use crate::registers::*;
use crate::security::SnpSecretsPageLayout;
use crate::snp::percpu::StackPages;
use crate::snp::SnpCoreSharedMem;
use crate::vbox::{MutFnTrait, MutFnWithCSTrait, VBox};

verus! {
#[vbit_struct(SevFeatures, u64)]
pub struct SevFeaturesSpec {
    #[vbits(0, 0)]
    snp: u64,
    #[vbits(1, 1)]
    vtom: u64,
    #[vbits(2, 2)]
    reflectvc: u64,
    #[vbits(3, 3)]
    restrict_inj: u64,
    #[vbits(4, 4)]
    alternate_inj: u64,
    #[vbits(7, 7)]
    btb_isolation: u64,
    #[vbits(9, 9)]
    secure_tsc: u64,
}
}

verismo_simple! {
#[derive(VPrint)]
#[repr(C, align(1))]
pub struct VmsaSegmentRegister {
    pub selector: u16,
    pub attr: u16,
    pub limit: u32,
    pub base: u64,
}

#[derive(SpecGetter, SpecSetter, VPrint)]
#[repr(C, align(1))]
/// Virtual Machine Saving Area for world switches
pub struct Vmsa {
    pub es: VmsaSegmentRegister,
    pub cs: VmsaSegmentRegister,
    pub ss: VmsaSegmentRegister,
    pub ds: VmsaSegmentRegister,
    pub fs: VmsaSegmentRegister,
    pub gs: VmsaSegmentRegister,
    pub gdtr: VmsaSegmentRegister,
    pub reserved_ldtr_idtr_tr: Array<u8, 90>,

    #[def_offset]
    pub vmpl: u8,
    pub cpl: u8,

    pub reserved2: Array<u8, 4>,

    pub efer: u64,

    pub reserved3: Array<u8, 112>,

    pub cr4: u64,
    pub cr3: u64,
    pub cr0: u64,
    pub reserved_dr7_6: Array<u8, 16>,
    pub rflags: u64,
    pub rip: u64,

    pub reserved4: Array<u8, 88>,

    pub rsp: u64,

    pub reserved5: Array<u8, 24>,

    #[def_offset]
    pub rax: u64,

    pub reserved6: Array<u8, 104>,

    pub gpat: u64,

    pub reserved7: Array<u8, 152>,

    #[def_offset]
    pub rcx: u64,
    #[def_offset]
    pub rdx: u64,
    #[def_offset]
    pub rbx: u64,

    pub reserved8: Array<u8, 8>,

    pub rbp: u64,
    pub rsi: u64,
    pub rdi: u64,
    //pub r8: u64,

    pub reserved_9_r9_15_exits_scratch: Array<u8, 112>,

    pub sev_features: u64,
    pub vintr_ctrl: u64,

    #[def_offset]
    pub guest_error_code: u64,

    pub virtual_tom: u64,

    pub reserved_12: Array<u8, 24>,
    pub xcr0: u64,

    pub reserved13: [u8; 3088],
}
}

pub type VmsaPage = Vmsa;

verus! {
proof fn proof_vmsa_size()
ensures
    spec_size::<VmsaPage>() == spec_cast_integer::<_, nat>(PAGE_SIZE!())
{}
}

def_asm_addr_for! {
    ap_entry_addr = ap_entry
}

verus! {
#[derive(IsConstant, WellFormed, SpecSize, VTypeCastSec)]
pub struct PerCpuData<'a> {
    pub secret: &'a SnpSecretsPageLayout,
    pub cpu: u32,
    pub resvd: u32,
}
}

verus! {
impl<'a> PerCpuData<'a> {
    pub open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& self.secret.wf_mastersecret()
    }
}
}

verus! {
    pub open spec fn ensures_init_ap_vmsa(
        vmsa: Vmsa, new_vmsa: Vmsa, cpu: VBox<PerCpuData>, cs: SnpCoreSharedMem, newcs: SnpCoreSharedMem
    ) -> bool {
        &&& newcs.inv_ac()
        &&& newcs.only_lock_reg_updated(cs, set![], set![spec_ALLOCATOR_lockid()])
        &&& vmsa.is_constant() ==> new_vmsa.is_constant()
        &&& (new_vmsa.rdi@.val) == cpu.id()
        &&& (new_vmsa.rsp@.val) != 0
        &&& (new_vmsa.vmpl@.val == 0)
    }

    pub open spec fn requires_init_ap_vmsa(cpu: VBox<PerCpuData>, gdt: &GDT, cs: SnpCoreSharedMem) -> bool {
        &&& cs.inv_ac()
        &&& gdt@.is_constant()
        &&& cpu.wf()
        &&& cpu@.inv()
    }

    fn init_ap_vmsa<'a>(
        vmsa: &mut Vmsa,
        cpu: VBox<PerCpuData>,
        gdt: &GDT,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    )
    requires
        requires_init_ap_vmsa(cpu, gdt, *old(cs))
    ensures
        ensures_init_ap_vmsa(*old(vmsa), *vmsa, cpu, *old(cs), *cs),
    {
        let stack = VBox::<StackPages>::new_aligned_uninit(PAGE_SIZE, Tracked(cs));

        // Copy control registers
        vmsa.efer = Msr{reg: MSR_EFER_BASE.into()}.read(
            Tracked(cs.snpcore.regs.tracked_borrow(RegName::MSR(MSR_EFER_BASE))));
        vmsa.xcr0 = XCR0.read(Tracked(cs.snpcore.regs.tracked_borrow(RegName::XCr0)));
        vmsa.cr0 = CR0.read(Tracked(cs.snpcore.regs.tracked_borrow(RegName::Cr0)));
        vmsa.cr3 = CR3.read(Tracked(cs.snpcore.regs.tracked_borrow(RegName::Cr3)));
        vmsa.cr4 = CR4.read(Tracked(cs.snpcore.regs.tracked_borrow(RegName::Cr4)));

        // Set AP entry address
        vmsa.rip = ap_entry_addr().into();
        // Default PAT
        vmsa.gpat = crate::pgtable_e::PAT_RESET_VAL.into();
        vmsa.rdi = cpu.into_raw().0.as_u64().into();
        // Set stack end addr
        vmsa.rsp = (stack.into_raw().0.to_usize() + size_of::<StackPages>()).into();
        // Enable SNP
        // Use restricted injection
        let sev_features = SevFeatures::empty().set_snp(1u64)
            .set_vtom(0u64)
            .set_reflectvc(0u64)
            .set_restrict_inj(1u64)
            .set_alternate_inj(0u64);
        vmsa.sev_features = sev_features.value.into();
        vmsa.vmpl = 0u64.into();

        // Reuse GDT
        let gdtr = GdtBaseLimit.read(
            Tracked(cs.snpcore.regs.tracked_borrow(RegName::GdtrBaseLimit)));
        vmsa.gdtr.base = gdtr.base;
        vmsa.gdtr.limit = gdtr.limit.into();
        //let gdt_ptr = SnpPPtr::from_usize(gdtr.base as usize);
        //let gdt = gdt_ptr.borrow(Tracked(gdt_perm));
        fill_seg(&mut vmsa.cs, gdt, GDT_KERNEL_CS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut vmsa.es, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut vmsa.ss, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut vmsa.ds, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);

    }
}

verus! {
pub struct InitApVmsa;
pub struct InitAPParams<'a> {
    pub fun: InitApVmsa,
    pub cpu: VBox<PerCpuData<'a>>,
    pub gdt: &'a GDT,
}
pub type InitAPOut = u8;

impl<'a, 'b> MutFnWithCSTrait<'a, SnpCoreSharedMem, InitAPParams<'b>, InitAPOut> for VmsaPage {
    open spec fn spec_update_cs_requires(&self, params: InitAPParams<'b>, cs: SnpCoreSharedMem) -> bool {
        requires_init_ap_vmsa(params.cpu, params.gdt, cs)
    }

    open spec fn spec_update_cs(&self, prev: &Self,
        params: InitAPParams<'b>, oldcs: SnpCoreSharedMem,
        ret: InitAPOut, cs: SnpCoreSharedMem) -> bool {
        ensures_init_ap_vmsa(*prev, *self, params.cpu, oldcs, cs)
    }

    fn box_update_cs(&'a mut self, params: InitAPParams<'b>, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: u8)
    {
        init_ap_vmsa(self, params.cpu, params.gdt, Tracked(cs));
        0
    }
}
}

verus! {
    pub fn fill_seg(
        seg: &mut VmsaSegmentRegister,
        gdt: &GDT,
        gdt_idx: usize_t,
        limit: u32_t,
        base: u64_t,
    )
    requires
        gdt_idx < gdt@.len(),
        gdt@.is_constant(),
    ensures
        seg.is_constant(),
    {
        assert(gdt_idx < 32);
        let selector = (gdt_idx * 8usize);
        let entry = Descriptor{value: (*gdt.index(gdt_idx)).into()};
        let attr: u16 = (entry.get_attr_0_7() as u16) | (entry.get_attr_8_11() << 8u64) as u16;
        seg.selector = selector.into();
        seg.attr = attr.into();
        seg.limit = limit.into();
        seg.base = base.into();
    }
}

verus! {
pub struct UpdateRichOSVmsa<'a> {
    pub gdt: &'a GDT,
    pub gdtr_addr: u64,
    pub bp_addr: u64,
    pub kernel_addr: u64,
    pub vmpl: u8,
}
}

verismo_simple! {
pub struct UpdateRichOSVmsaOut;
impl<'a, 'b> MutFnTrait<'a, UpdateRichOSVmsa<'b>, UpdateRichOSVmsaOut> for VmsaPage {
    open spec fn spec_update_requires(&self, params: UpdateRichOSVmsa<'b>) -> bool {
        &&& params.gdt.is_constant()
    }

    open spec fn spec_update(&self, prev: &Self, params: UpdateRichOSVmsa<'b>, ret: UpdateRichOSVmsaOut) -> bool {
        let UpdateRichOSVmsa{gdt, vmpl, gdtr_addr, bp_addr, kernel_addr} = params;
        &&& prev.is_constant() ==> self.is_constant()
        &&& (self.gdtr.base as int) == gdtr_addr
        &&& self.vmpl == vmpl
        &&& self.rip == kernel_addr
        &&& self.rsi == bp_addr
    }

    fn box_update(&'a mut self, params: UpdateRichOSVmsa<'b>) -> (ret: UpdateRichOSVmsaOut)
    {
        let UpdateRichOSVmsa{gdt, vmpl, gdtr_addr, bp_addr, kernel_addr} = params;

        self.guest_error_code = 0xfff;
        self.gpat = crate::pgtable_e::PAT_RESET_VAL.into();
        self.rsi= bp_addr.into();
        self.cr0 = 1; // enable protected mode
        self.rflags = 2;
        self.xcr0 = 1;
        self.efer = 0x1000;
        self.rip = kernel_addr.into();

        let gdt_size: u32 = size_of::<GDT>() as u32;
        self.gdtr.base = gdtr_addr.into();
        self.gdtr.limit = gdt_size - 1;
        self.gdtr.selector = 0;
        self.gdtr.attr = 0;
        fill_seg(&mut self.cs, gdt, GDT_KERNEL_CS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut self.es, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut self.ss, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);
        fill_seg(&mut self.ds, gdt, GDT_KERNEL_DS, GDTR_LIMIT, GDTR_BASE);

        let sev_features = SevFeatures::empty().set_snp(1u64_t)
            .set_vtom(0u64_t)
            .set_reflectvc(0u64_t)
            .set_restrict_inj(1u64_t)
            .set_alternate_inj(0u64_t);
        self.sev_features = sev_features.value.into();
        self.vmpl = vmpl.into();
        UpdateRichOSVmsaOut
    }
}
}

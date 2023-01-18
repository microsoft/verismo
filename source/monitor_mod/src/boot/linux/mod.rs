use alloc::vec::Vec;

use crate::addr_e::*;
use crate::arch::addr_s::PAGE_SIZE;
use crate::boot::monitor_params::*;
use crate::boot::params::*;
use crate::debug::VPrintAtLevel;
use crate::global::spec_ALLOCATOR_lockid;
use crate::pgtable_e::*;
use crate::ptr::*;
use crate::security::*;
use crate::snp::cpu::*;
use crate::snp::cpuid::SnpCpuidTable;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::vbox::*;
use crate::*;

verismo_simple! {
#[repr(C, align(1))]
#[derive(SpecGetter, SpecSetter)]
pub struct BootInfo {
    #[def_offset]
    pub bp: BootParams,
    #[def_offset]
    pub secret: SnpSecretsPageLayout,
    #[def_offset]
    pub cpuid: SnpCpuidTable,
    #[def_offset]
    pub gdt: GDT,
    #[def_offset]
    pub cmdline: [u8; 256],
    #[def_offset]
    pub ccblob: CCBlobSevInfo, // 40
    pub reserved: [u8; {4096 - 48 - 256 - 256}], //4096 - 40 - 256 - 256 (32 * 8)
}

#[repr(C, align(1))]
#[derive(Copy, VClone)]
pub struct CCBlobSevInfo {
    pub reserved0: u32,
    pub reserved0_1: u16,
    pub reserved1: u16,
    pub secrets_phys: u64,
    pub secrets_len: u32,
    pub reserved2: u32,
    pub cpuid_phys: u64,
    pub cpuid_len: u32,
    pub reserved3: u32,
    pub shared_page: u64,
}
}

verus! {
proof fn lemma_boot_info_size()
ensures
    spec_size::<BootInfo>() > PAGE_SIZE,
{}
}

verus! {
pub struct BootUpdate<'a> {
    pub acpi_rsdp_addr: u64,
    pub cc_blob_addr: u64,
    pub cmd_line_addr: u64,
    pub cmdline_size: u64,
    pub e820_entries: u8,
    pub e820: &'a ValidatedE820Table,
    pub hdr: &'a SetupHeader,
}


use crate::vbox::MutFnTrait;
impl<'a, 'b> MutFnTrait<'a, BootUpdate<'b>, u8> for BootParams {
    open spec fn spec_update_requires(&self, params: BootUpdate<'b>) -> bool {
        &&& params.e820.is_constant()
        &&& params.hdr.is_constant()
        &&& params.e820@.len() >= params.e820_entries
        &&& self.is_constant()
    }

    open spec fn spec_update(&self, prev: &Self, params: BootUpdate<'b>, ret: u8) -> bool {
        &&& self.is_constant()
        &&& self.e820_entries.spec_eq(params.e820_entries)
        &&& self.e820@.take(params.e820_entries as int) =~~= params.e820@.take(params.e820_entries as int)
    }

    fn box_update(&'a mut self, params: BootUpdate<'b>) -> (ret: u8)
    {
        let BootUpdate{
            acpi_rsdp_addr, cc_blob_addr, cmd_line_addr, cmdline_size,
            e820_entries, e820, hdr
        } = params;
        self.acpi_rsdp_addr = acpi_rsdp_addr.into();
        self.cc_blob_addr = cc_blob_addr.into();
        self._ext_cmd_line_ptr = ((cmd_line_addr >> 32u64) as u32).into();
        self.hdr = hdr.clone();
        self.hdr.cmd_line_ptr = (cmd_line_addr as u32).into();
        self.hdr.cmdline_size = cmdline_size.into();
        self.e820_entries = e820_entries.into();
        let ghost oldself = *self;
        let mut i = 0;
        while i < e820_entries
        invariant
            0 <= i <= e820_entries,
            self.is_constant(),
            e820.is_constant(),
            e820_entries <= e820@.len(),
            self.e820@.take(i as int) =~~=  e820@.take(i as int),
            *self === oldself.spec_set_e820(self.e820),
        {
            proof {
                assert(
                    self.e820@.update(i as int, e820[i as int]).take(i as int + 1) =~~=
                    self.e820@.take(i as int).push(e820[i as int])
                );
                assert(e820@.take(i as int + 1) =~~= e820@.take(i as int).push(e820[i as int]));

            }
            self.e820.update(i as usize, e820.index(i as usize).clone());
            proof{assert(self.e820@.is_constant());}
            i = i + 1;
        }
        0
    }
}
}

verus! {
/// Use 32-bit boot protocol
/// https://www.kernel.org/doc/html/latest/x86/boot.html#bit-boot-protocol

pub struct SetBasicBootInfoParam<'a> {
    pub mparam: &'a MonitorParams,
    pub vmpl: u8,
    pub richos_boot: &'a BootParams,
    pub cc_blob_addr: u64,
    pub cmd_line_addr: u64,
}

impl<'a> MutFnTrait<'a, SetBasicBootInfoParam<'a>, u8> for BootInfo {
open spec fn spec_update_requires(&self, params: SetBasicBootInfoParam) -> bool {
    &&& params.mparam.mp_wf()
    &&& 1 <= params.vmpl < 4
    &&& params.richos_boot.is_constant()
    &&& self.is_constant()
}

open spec fn spec_update(&self, prev: &Self, params: SetBasicBootInfoParam<'a>, ret: u8) -> bool {
    &&& self.is_constant()
    &&& *self === prev.spec_set_bp(self.bp).spec_set_gdt(self.gdt).spec_set_cmdline(self.cmdline)
    &&& self.bp.e820_entries <= self.bp.e820@.len()
}

fn box_update(&'a mut self, params: SetBasicBootInfoParam<'a>) -> (ret: u8)
{
    let SetBasicBootInfoParam{
        vmpl, mparam, richos_boot, cmd_line_addr, cc_blob_addr
    } = params;

    let richos_start: u64 = mparam.richos_start.into();
    let e820_entries: u8 = mparam.validated_entries.into();
    let cmdline_size: u64 = mparam.richos_cmdline_len.into();
    // Init GDT
    self.gdt.set(0, Descriptor::empty().value.into());
    self.gdt.set(1, Descriptor::entry_cs_sys().value.into());
    self.gdt.set(2, Descriptor::entry_cs_user().value.into());
    self.gdt.set(3, Descriptor::entry_ds_sys().value.into());
    self.gdt.set(4, Descriptor::entry_ds_user().value.into());
    self.bp.box_update(BootUpdate{
        acpi_rsdp_addr: mparam.acpi.into(),
        cc_blob_addr, cmd_line_addr, cmdline_size,
        e820_entries,
        e820: &mparam.validated_e820,
        hdr: &richos_boot.hdr}
    );
    self.cmdline = mparam.richos_cmdline.clone();
    0
}
}

pub struct SetSnpBootInfoParam<'a> {
    pub vmpl: u8,
    pub secret_addr: usize,
    pub master_secret: &'a SnpSecretsPageLayout,
    pub cpuid_addr: usize,
    pub early_shared: VBox<OnePage>,
    pub cpuid: &'a SnpCpuidTable
}

impl<'a> MutFnTrait<'a, SetSnpBootInfoParam<'a>, u8> for BootInfo {
open spec fn spec_update_requires(&self, params: SetSnpBootInfoParam<'a>) -> bool {
    &&& 1 <= params.vmpl < 4
    &&& params.early_shared.is_shared_page()
    &&& params.master_secret.wf_mastersecret()
    &&& self.secret.is_constant()
}

open spec fn spec_update(&self, prev: &Self, params: SetSnpBootInfoParam<'a>, ret: u8) -> bool {
    &&& self.secret.is_constant_to(params.vmpl as nat)
    &&& self.ccblob.is_constant()
    &&& self.cpuid === *params.cpuid
    &&& *self === prev.spec_set_secret(self.secret).spec_set_ccblob(self.ccblob).spec_set_cpuid(self.cpuid)
}

fn box_update(&'a mut self, params: SetSnpBootInfoParam<'a>) -> (ret: u8)
{
    let SetSnpBootInfoParam {master_secret, vmpl, secret_addr, cpuid_addr, cpuid, early_shared} = params;

    self.ccblob = CCBlobSevInfo::new(
        secret_addr as u64,
        cpuid_addr as u64,
        early_shared);
    self.secret.box_update(FillSecretForVMPL{master_secret, vmpl});
    self.cpuid = cpuid.clone();
    0
}
}

pub struct SetMemoryBootInfoParam {
    pub vmpl: u8,
}

impl<'a> MutFnWithCSTrait<'a, SnpCoreSharedMem, SetMemoryBootInfoParam, OSMem> for BootInfo {
open spec fn spec_update_cs_requires(&self, params: SetMemoryBootInfoParam, cs: SnpCoreSharedMem) -> bool {
    &&& 1 <= params.vmpl < 4
    &&& self.bp.is_constant()
    &&& self.bp.e820_entries <= self.bp.e820@.len()
    &&& cs.inv()

}

open spec fn spec_update_cs(&self, prev: &Self, params: SetMemoryBootInfoParam,
    oldcs: SnpCoreSharedMem, ret: OSMem, cs: SnpCoreSharedMem) -> bool {
    &&& *self === prev.spec_set_bp(self.bp)
    &&& self.bp === prev.bp.spec_set_e820(self.bp.e820).spec_set_e820_entries(self.bp.e820_entries)
    &&& osmem_wf(ret@)
    &&& self.bp.is_constant()
    &&& cs.inv()
    &&& cs.only_lock_reg_coremode_updated(oldcs, set![], set![spec_ALLOCATOR_lockid()])
}

fn box_update_cs(
    &'a mut self, params: SetMemoryBootInfoParam, Tracked(cs): Tracked<&mut SnpCoreSharedMem>
) -> (ret: OSMem)
{
    let mut n = self.bp.e820_entries.into();
    let ret = add_ram_from_allocator(params.vmpl, &mut self.bp.e820, &mut n, Tracked(cs));
    self.bp.e820_entries = n.into();
    let mut osmem;
    match ret {
        Ok(tmposmem) => {
            osmem = tmposmem;
        }
        _ => {
            new_strlit("Err from osmem_add_ram_from_allocator\n").leak_debug();
            vc_terminate(SM_TERM_MEM, Tracked(&mut cs.snpcore));
        }
    }
    assert(self.bp.e820@.is_constant());
    assert(self.bp.e820_entries.is_constant());
    osmem
}
}
}

verismo_simple! {
impl CCBlobSevInfo{
    fn new(secret_addr: u64_t, cpuid_addr: u64_t, shared: VBox<OnePage>) -> (retccblob: CCBlobSevInfo)
    requires
        shared.is_shared_page(),
    ensures
        retccblob.is_constant(),
    {
        let (shared_addr, _) = shared.into_raw();
        CCBlobSevInfo {
            reserved0: 0,
            reserved0_1: 0,
            reserved1: 0,
            secrets_phys: secret_addr.into(),
            secrets_len: PAGE_SIZE.into(),
            reserved2: 0,
            cpuid_phys: cpuid_addr.into(),
            cpuid_len: PAGE_SIZE.into(),
            reserved3: 0,
            shared_page: shared_addr.as_u64().into(),
        }
    }
}
}

verus! {
pub fn load_bzimage_to_vmsa(
    osmem: &mut Vec<OSMemEntry>,
    mparam: &MonitorParams,
    vmpl: u8,
    master_secret: &SnpSecretsPageLayout,
    cpuid: VBox<SnpCpuidTable>,
    hvparam: VBox<OnePage>,
    early_shared: VBox<OnePage>,
    Tracked(richos_perm): Tracked<SnpPointsToRaw>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>
) -> (retbox: (VBox<VmsaPage>, VBox<SnpCpuidTable>))
requires
    osmem_wf(old(osmem)@),
    early_shared.is_shared_page(),
    hvparam.is_default_page(),
    hvparam@.is_constant(),
    mparam.mp_wf(),
    mparam.richos_size > 0,
    vmpl == RICHOS_VMPL,
    master_secret.wf_mastersecret(),
    cpuid@.is_constant(),
    cpuid.snp().is_vmpl0_private(),
    richos_perm@.wf_const_default((mparam.richos_start.vspec_cast_to(), mparam.richos_size.vspec_cast_to())),
    (*old(cs)).inv(),
ensures
    osmem_wf(osmem@),
    (*cs).inv(),
    (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![spec_ALLOCATOR_lockid()]),
    retbox.1 === cpuid,
    retbox.0.is_default_page(),
    retbox.0@.is_constant(),
    retbox.0@.vmpl@.val == vmpl,
{
    let ghost cs1 = *cs;
    let mut vmsa  = VBox::<VmsaPage>::new_aligned_uninit(PAGE_SIZE, Tracked(cs));

    let richos_size: usize = mparam.richos_size.into();
    let richos_start: usize = mparam.richos_start.into();

    if richos_start == 0 || richos_size <= size_of::<BootParams>() {
        new_strlit("Invalid richos load address or size\n").leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
    }
    //verismo::snp::secret::measure(richos_start, richos_size, state);
    let tracked (boot_perm, richos_perm) = richos_perm.trusted_split(spec_size::<BootParams>());
    let richos_boot = VBox::<BootParams>::from_raw(richos_start, Tracked(boot_perm.tracked_into()));

    let ghost cs2 = *cs;
    let mut bootinfo = VBox::<BootInfo>::new_aligned_uninit(PAGE_SIZE, Tracked(cs));
    let (bootinfo_ptr, Tracked(bootinfo_perm)) = bootinfo.into_raw();
    let secret_addr = bootinfo_ptr.secret().to_usize();
    let cpuid_addr = bootinfo_ptr.cpuid().to_usize();
    let gdtr_addr: u64 = bootinfo_ptr.gdt().as_u64();
    let bp_addr: u64 = bootinfo_ptr.bp().as_u64();
    let cc_blob_addr: u64 = bootinfo_ptr.ccblob().as_u64();
    let cmd_line_addr: u64 = bootinfo_ptr.cmdline().as_u64();
    let mut bootinfo = VBox::<BootInfo>::from_raw(bootinfo_ptr.to_usize(), Tracked(bootinfo_perm));

    assert(bootinfo@.is_constant());
    bootinfo.box_update(SetBasicBootInfoParam{
        vmpl, mparam, cc_blob_addr, cmd_line_addr, richos_boot: richos_boot.borrow()
    });

    let (_, Tracked(boot_perm)) = richos_boot.into_raw();
    proof{richos_perm = boot_perm.tracked_into_raw().trusted_join(richos_perm);}
    bootinfo.box_update(SetSnpBootInfoParam{vmpl, early_shared, master_secret, secret_addr, cpuid_addr, cpuid: cpuid.borrow()});
    let ghost cs3 = *cs;
    let mut tmposmem = bootinfo.box_update_cs(SetMemoryBootInfoParam{vmpl}, Tracked(cs));
    proof{
        cs1.lemma_update_prop(cs2, cs3, set![], set![spec_ALLOCATOR_lockid()], set![], set![spec_ALLOCATOR_lockid()]);
        cs1.lemma_update_prop(cs3, *cs, set![], set![spec_ALLOCATOR_lockid()], set![], set![spec_ALLOCATOR_lockid()]);
    }
    osmem.append(&mut tmposmem);
    assert(osmem_wf(osmem@));
    let bi = bootinfo.borrow();

    bi.bp.e820.leak_debug();

    let prefer_vaddr: usize = bi.bp.hdr.pref_address.into();
    let setup_sects: usize  = bi.bp.hdr.setup_sects.into();
    let start32_offset: usize = (1usize + setup_sects) * 512;
    let start32_addr: usize = start32_offset + richos_start;

    if start32_offset >= richos_size {
        new_strlit("Invalid richos start32_offset\n").leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
    }

    if prefer_vaddr % PAGE_SIZE != 0 {
        new_strlit("Invalid richos prefer_vaddr\n").leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
    }

    let kernel_size: usize = richos_size - start32_offset;
    if !prefer_vaddr.check_valid_addr(kernel_size) {
        new_strlit("Invalid richos prefer_vaddr\n").leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
    }

    let prefer_vaddr = prefer_vaddr.to_page().to_addr();

    let tracked (left, start32_perm) = richos_perm.trusted_split(start32_offset as nat);
    // Fixed #HV error due to uninitialized mem
    if let Some(i) = osmem_find(osmem, prefer_vaddr.to_page()) {
        proof{
            assert(osmem[i as int].wf());
        }
        let end_page = osmem[i].end();
        if prefer_vaddr + kernel_size > end_page.to_addr() {
            new_strlit("No enough Ram for kernel: ").leak_debug();
            vc_terminate(SM_TERM_MEM, Tracked(&mut cs.snpcore));
        }
        let mut entry = osmem.remove(i);
        let npages = if kernel_size % PAGE_SIZE == 0 {
            kernel_size.to_page()
        } else {
            kernel_size.to_page() + 1
        };
        let (left, mut entry, right) = osmem_entry_split(entry, (prefer_vaddr).to_page() as usize, npages as usize);
        let Tracked(mut prefer_mem) = entry.page_perms;
        proof{
            assert(entry.wf());
            entry.proof_open_wf();
            let start = (prefer_vaddr as int).to_page();
            let end_page = ((prefer_vaddr  + kernel_size) as int).to_page();
            assert forall |i: int| start <= i < end_page
            implies
                prefer_mem.contains_key(i)
            by {
                assert(entry.spec_start() <= i < entry.spec_end());
                entry.proof_contains(i);
            }
            assert forall |i: int| prefer_mem.contains_key(i)
            implies
                prefer_mem[i]@.wf_not_null((i.to_addr(), PAGE_SIZE as nat))
                && entry.spec_start() <= i < entry.spec_end()
            by {
                entry.proof_contains(i);
            }
        }
        let ghost old_entry = entry;
        let ghost old_prefer_mem = prefer_mem;
        new_strlit("copy image\n").leak_debug();
        mem_copy_to_pages(start32_addr as usize, prefer_vaddr, kernel_size as usize, Tracked(&start32_perm), Tracked(&mut prefer_mem));
        proof{
            assert forall |i| #[trigger] prefer_mem.contains_key(i)
            implies
                spec_contains_page_perm(prefer_mem, i, entry.spec_osperm())
            by {
                old_entry.proof_contains(i);
                assert(old_prefer_mem.contains_key(i));
                let page_perm = prefer_mem[i]@;
                let old_page_perm = old_prefer_mem[i]@;
                assert(spec_contains_page_perm(old_prefer_mem, i, old_entry.spec_osperm()));
                assert(prefer_vaddr <= i.to_addr());
                let start = spec_mem_copy_onepage_start(i, prefer_vaddr as int, kernel_size as nat);
                let end = spec_mem_copy_onepage_end(i, prefer_vaddr as int, kernel_size as nat);
                let b1 = start32_perm@.bytes().subrange(start, end as int);
                assert(start32_perm@.bytes().len() == kernel_size);
                proof_subrange_is_constant_to(start32_perm@.bytes(), start, kernel_size as int, vmpl as nat);
                let b2 = old_page_perm.bytes().skip(b1.len() as int);
                assert (b1.len() <= PAGE_SIZE);
                proof_subrange_is_constant_to(old_page_perm.bytes(), b1.len() as int, PAGE_SIZE as int, vmpl as nat);
                proof_bytes_add_is_constant_to(b1, b2, vmpl as nat);
                assert(page_perm.bytes().is_constant_to(vmpl as nat));
            }
            assert(old_prefer_mem.dom() =~~= Set::new(|i: int| entry.spec_start() <= i < entry.spec_end()));
            assert(prefer_mem.dom() =~~= Set::new(|i: int| entry.spec_start() <= i < entry.spec_end()));
        }
        entry.page_perms = Tracked(prefer_mem);
        proof{
            entry.proof_open_wf();
            assert(entry.wf());
        }

        let entry  = osmem_entry_merge(left, entry);
        let entry  = osmem_entry_merge(entry, right);
        osmem.insert(i, entry);
        assert(osmem_wf(osmem@));
    } else {
        new_strlit("Bad prefer_vaddr\n").leak_debug();
        vc_terminate(SM_TERM_MEM, Tracked(&mut cs.snpcore));
    }

    vmsa.box_update(UpdateRichOSVmsa{
        vmpl, gdt: &bootinfo.borrow().gdt, gdtr_addr, bp_addr, kernel_addr: prefer_vaddr as u64});

    proof{assert(bootinfo@.is_constant_to(vmpl as nat));}
    let (bootinfo_ptr, Tracked(bootinfo_perm)) = bootinfo.into_raw();
    proof{
        proof_into_is_constant_to::<_, SecSeqByte>(bootinfo_perm@.value(), vmpl as nat);
    }
    let tracked raw_perm = bootinfo_perm.tracked_into_raw();
    assert(raw_perm@.bytes().is_constant_to(vmpl as nat));
    let start_page = bootinfo_ptr.to_usize().to_page();
    let npages = size_of::<BootInfo>() / PAGE_SIZE;
    let tracked page_perms = raw_perm.tracked_to_pages();
    proof {
        assert forall |i| start_page <= i < (start_page + npages)
        implies
        #[trigger]page_perms.contains_key(i) &&
        page_perms[i]@.wf_default((i.to_addr(), PAGE_SIZE as nat)) &&
        page_perms[i]@.bytes().is_constant_to(vmpl as nat)
        by {
            assert(page_perms.contains_key(i));
            assert(page_perms[i]@.bytes() =~~= raw_perm@.bytes().subrange((i - start_page).to_addr(), (i - start_page).to_addr() + PAGE_SIZE));
        }
    }
    osmem_add(
        osmem, bootinfo_ptr.to_usize().to_page(),
        size_of::<BootInfo>() / PAGE_SIZE, OSMemPerm::ram(), false,
        Tracked(page_perms), Tracked(&mut cs.snpcore));

    // Add hvparam page into osmem
    let (hvparam_ptr, Tracked(hvparam_perm)) = hvparam.into_raw();
    let hvparam_page: usize = hvparam_ptr.to_usize().to_page();
    let tracked mut hvparam_perms = Map::tracked_empty();
    let tracked hvparam_perm = hvparam_perm.tracked_into_raw();
    proof{
        hvparam_perms.tracked_insert(hvparam_page as int, hvparam_perm);
    }
    proof {
        assert(hvparam_perm@.wf_default(((hvparam_page as int).to_addr(), PAGE_SIZE as nat)));
        assert(hvparam_perm@.bytes().is_constant_to(vmpl as nat));
        assert forall |i| hvparam_page <= i < (hvparam_page + 1)
        implies
        #[trigger]hvparam_perms.contains_key(i) &&
        hvparam_perms[i]@.wf_default((i.to_addr(), PAGE_SIZE as nat)) &&
        hvparam_perms[i]@.bytes().is_constant_to(vmpl as nat)
        by {}
    }
    osmem_add(
        osmem, hvparam_page, 1, OSMemPerm::readonly(), false,
        Tracked(hvparam_perms), Tracked(&mut cs.snpcore));

    let mut i = 0;
    while i < osmem.len() {
        osmem[i].leak_debug();
        i = i + 1;
    }
    (vmsa, cpuid)
}
}

use crate::allocator::VeriSMoAllocator;
use crate::arch::addr_s::PAGE_SIZE;
use crate::arch::reg::RegName;
use crate::boot::idt::init_idt;
use crate::boot::init::{init_mem, InitMem};
use crate::boot::monitor_params::{MonitorParamGlobalPerms, MonitorParamPerms, MonitorParams};
use crate::debug::Console;
use crate::global::*;
use crate::lock::{LockPermRaw, MapLockContains, MapRawLockTrait};
use crate::mem::{RawMemPerms, SnpMemCoreConsole};
use crate::mshyper::{hyperv_register, GhcbHyperPageHandle, HyperPageHandle};
use crate::pgtable_e::TrackedPTEPerms;
use crate::ptr::{SnpMemAttrTrait, SnpPPtr, SnpPointsTo, SwSnpMemAttr};
use crate::registers::*;
use crate::security::{SnpGuestChannel, SnpSecretsPageLayout, RICHOS_VMPL};
use crate::snp::cpu::{PerCpuData, *};
use crate::snp::cpuid::init_cpu_for_crypto;
use crate::snp::ghcb::GhcbHandle;
use crate::snp::percpu::BSP;
use crate::snp::{SnpCoreConsole, SnpCoreSharedMem};
use crate::tspec::*;
use crate::tspec_e::*;
use crate::vbox::VBox;

verus! {

/// AP entry
#[no_mangle]
pub extern "C" fn ap_call(
    cpu: &PerCpuData,
    Tracked(cs): Tracked<SnpCoreSharedMem>,
    Tracked(nextvmpl_id): Tracked<CoreIdPerm>,
)
    requires
        nextvmpl_id@.vmpl == RICHOS_VMPL as nat,
        cs.inv_stage_ap_wait(),
{
    use crate::debug::VPrintAtLevel;
    let tracked mut cs = cs;
    let cpu_id = cpu.cpu as usize;
    (new_strlit("ap call "), cpu_id).leak_debug();
    new_strlit("ap alloc_ghcb_handle").leak_debug();
    let ghcb = GhcbHandle::alloc_ghcb_handle(Tracked(&mut cs));
    let (hyperv, ghcb) = HyperPageHandle::new_shared_page(PAGE_SIZE, ghcb, Tracked(&mut cs));
    let (guest_channel, ghcb) = SnpGuestChannel::new(ghcb, Tracked(&mut cs));
    let ghcb_hv_h = GhcbHyperPageHandle(ghcb, hyperv);
    let mut vmsa: VBox<VmsaPage>;
    loop
        invariant
            cs.inv_stage_ap_wait(),
        ensures
            vmsa.is_vmsa_page(),
    {
        let tracked mut vmsa_lock = cs.lockperms.tracked_remove(spec_RICHOS_VMSA_lockid());
        let (vmsa_vec_ptr, Tracked(mut vmsa_vec_perm), Tracked(mut vmsa_lock0)) =
            RICHOS_VMSA().acquire(Tracked(vmsa_lock), Tracked(&cs.snpcore.coreid));
        proof {
            vmsa_lock = vmsa_lock0;
        }
        let mut vmsa_vec = vmsa_vec_ptr.take(Tracked(&mut vmsa_vec_perm));
        let mut vmsa_opt: Option<VBox<VmsaPage>> = None;
        if vmsa_vec.len() > cpu_id {
            vmsa_opt = vmsa_vec.remove(cpu_id);
            vmsa_vec.insert(cpu_id, None);
        }
        vmsa_vec_ptr.put(Tracked(&mut vmsa_vec_perm), vmsa_vec);
        RICHOS_VMSA().release(
            Tracked(&mut vmsa_lock),
            Tracked(vmsa_vec_perm),
            Tracked(&cs.snpcore.coreid),
        );
        proof {
            cs.lockperms.tracked_insert(spec_RICHOS_VMSA_lockid(), vmsa_lock);
        }
        match vmsa_opt {
            Some(v) => {
                vmsa = v;
                break ;
            },
            _ => {},
        }
        crate::lock::fence();
    }
    new_strlit("start richos ap\n").leak_debug();
    crate::security::run_richos(
        ghcb_hv_h,
        guest_channel,
        vmsa,
        cpu.secret,
        Tracked(nextvmpl_id),
        Tracked(&mut cs),
    );
    loop {
    }
}

} // verus!
verus! {

pub open spec fn shared_mem_range() -> Map<int, (int, nat)> {
    map![
            spec_ALLOCATOR().lockid() => spec_ALLOCATOR().ptr_range(),
            spec_CONSOLE_lockid() => spec_CONSOLE_range(),
            spec_PT_lockid() => spec_PT_range(),
        ]
}

} // verus!
verus! {

impl SnpCoreSharedMem {
    // inv + allocator + console
    pub open spec fn inv_ac(&self) -> bool {
        &&& self.inv()
    }
}

} // verus!
verus! {

#[no_mangle]
#[verifier(external_body)]
// BSP starts with a set of snpcore for BSP at VMPL0 - VMPL4 and a set of snpcore for APs at VMPL0
pub extern "C" fn bsp_call(
    mp_ptr: crate::ptr::SnpPPtr<MonitorParams>,
    Tracked(mp_perms): Tracked<MonitorParamPerms>,
    Tracked(alloc_perm): Tracked<SnpPointsTo<VeriSMoAllocator>>,
    Tracked(memcc): Tracked<SnpMemCoreConsole>,
    Tracked(ap_ids): Tracked<Map<int, CoreIdPerm>>,
    Tracked(nextvmpl_ids): Tracked<Map<int, CoreIdPerm>>,
    Tracked(initial_locks): Tracked<Map<int, LockPermRaw>>,
    Tracked(preval_free_perms): Tracked<RawMemPerms>,
    Tracked(gdt_perm): Tracked<&SnpPointsTo<crate::snp::cpu::GDT>>,
)
    requires
        memcc.memperm.mem_perms_e820_invalid(mp_perms@.e820()),
        memcc.wf(),
        preval_free_perms.mem_perms_e820_valid(mp_perms@.e820()),
        preval_free_perms.wf(),
        mp_perms@.wf_at(mp_ptr),
        mp_ptr.is_constant(),
        is_alloc_perm(alloc_perm@),
        gdt_perm@.wf_const_default(
            memcc.cc.snpcore.regs[RegName::GdtrBaseLimit].val::<Gdtr>().base.vspec_cast_to(),
        ),
        initial_locks.contains_clean_locks(memcc.cc.snpcore.cpu(), shared_mem_range()),
        contains_PT(initial_locks),
        initial_locks[spec_PT_lockid()]@.is_unlocked(
            memcc.cc.snpcore.cpu(),
            spec_PT_lockid(),
            initial_locks[spec_PT_lockid()]@.points_to.range(),
        ),
        spec_ap_ids_wf(ap_ids, BSP as int),
        forall|i| spec_cpumap_contains_cpu(nextvmpl_ids, i, 1),
    ensures
        false,
{
    let tracked mut nextvmpl_ids = nextvmpl_ids;
    let tracked mut lockperms = initial_locks;
    assert(lockperms.contains_key(spec_CONSOLE_lockid()));
    let tracked mut alloc_lock = lockperms.tracked_remove(spec_ALLOCATOR_lockid());
    assert(alloc_lock === initial_locks[spec_ALLOCATOR_lockid()]);
    assert(spec_CONSOLE_lockid() != spec_ALLOCATOR_lockid());
    let tracked mut console_lock = lockperms.tracked_remove(spec_CONSOLE_lockid());
    let tracked mut pt_lock = lockperms.tracked_remove(spec_PT_lockid());
    assert(console_lock === initial_locks[spec_CONSOLE_lockid()]);
    let (mpbox, hvparam_page, Tracked(mut cc), Tracked(mut mp_gperms)) = init_mem(
        mp_ptr,
        Tracked(mp_perms),
        Tracked(alloc_perm),
        Tracked(&mut alloc_lock),
        Tracked(memcc),
        Tracked(preval_free_perms),
    );
    let mparam = mpbox.borrow();
    let tracked SnpCoreConsole { snpcore, console } = cc;
    proof {
        let tracked console = console.tracked_remove(0);
        console_lock.tracked_bind_new::<Console>(Console::invfn(), console.tracked_into());
        assert(Console::invfn()(console@.value()));
        assert(console_lock@.invfn.inv::<Console>(console@.value()));
        assert(pt_lock@.invfn.inv::<TrackedPTEPerms>(pt_lock@.points_to.value()));
    }
    let tracked mut lockperms = Map::tracked_empty();
    proof {
        lockperms.tracked_insert(spec_CONSOLE_lockid(), console_lock);
        lockperms.tracked_insert(spec_ALLOCATOR_lockid(), alloc_lock);
        lockperms.tracked_insert(spec_PT_lockid(), pt_lock);
        assert(lockperms.contains_key(spec_ALLOCATOR_lockid()));
    }
    let tracked mut cs = SnpCoreSharedMem { snpcore, lockperms };
    proof {
        assert(cs.snpcore.inv());
        assert(console_lock@.is_unlocked(
            cs.snpcore.cpu(),
            console_lock@.lockid(),
            console_lock@.ptr_range(),
        ));
        assert(alloc_lock@.is_unlocked(
            cs.snpcore.cpu(),
            alloc_lock@.lockid(),
            alloc_lock@.ptr_range(),
        ));
        assert(cs.wf_pt());
        assert(contains_ALLOCATOR(cs.lockperms));
        assert(contains_CONSOLE(cs.lockperms));
        assert(contains_PT(cs.lockperms));
    }
    init_idt(Tracked(&mut cs));
    let tracked MonitorParamGlobalPerms { cpuid, secret, richos, acpi } = mp_gperms;
    let cpuid_page = VBox::from_raw(mparam.cpuid_page.into(), Tracked(cpuid.tracked_into()));
    init_cpu_for_crypto(cpuid_page.borrow(), Tracked(&mut cs));
    let ghcb = GhcbHandle::alloc_ghcb_handle(Tracked(&mut cs));
    let (hyperv, ghcb) = HyperPageHandle::new_shared_page(PAGE_SIZE, ghcb, Tracked(&mut cs));
    let ghcb_hv_h = GhcbHyperPageHandle(ghcb, hyperv);
    let ghcb_hv_h = hyperv_register(ghcb_hv_h, Tracked(&mut cs));
    let secret_page = VBox::<SnpSecretsPageLayout>::from_raw(
        mparam.secret_page.into(),
        Tracked(secret.tracked_into()),
    );
    let gdtr = GdtBaseLimit.read(Tracked(cs.snpcore.regs.tracked_borrow(RegName::GdtrBaseLimit)));
    let gdt_ptr = SnpPPtr::from_usize(gdtr.base.into());
    let gdt = gdt_ptr.borrow(Tracked(gdt_perm));
    let mut ghcb_hv_h = ghcb_hv_h.start_all_ap(
        mparam.cpu_count.into(),
        secret_page.borrow(),
        gdt,
        Tracked(ap_ids),
        Tracked(&mut cs),
    );
    let GhcbHyperPageHandle(ghcb, hyperv) = ghcb_hv_h;
    let (guest_channel, ghcb) = SnpGuestChannel::new(ghcb, Tracked(&mut cs));
    assert(richos@.wf_const_default(
        (mparam.richos_start.vspec_cast_to(), mparam.richos_size.vspec_cast_to()),
    ));
    let tracked nextvmpl_id = nextvmpl_ids.tracked_remove(BSP as int);
    crate::security::start_richos(
        mparam,
        secret_page.borrow(),
        cpuid_page,
        hvparam_page,
        guest_channel,
        GhcbHyperPageHandle(ghcb, hyperv),
        Tracked(nextvmpl_id),
        Tracked(richos),
        Tracked(acpi),
        Tracked(&mut cs),
    );
    loop {
    }
}

} // verus!

use super::mshv_fmt::FmtHvParamCall;
use super::mshv_init::process_vm_mem;
use super::*;
use crate::allocator::VeriSMoAllocator;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::boot::init::e820_fmt::e820_format;
use crate::boot::monitor_params::MonitorParamGlobalPerms;
#[cfg(debug_assertions)]
use crate::boot::monitor_params::SimpleMonitorParams;
use crate::lock::{LockPermRaw, MapLockContains, MapRawLockTrait};
use crate::vbox::{MutFnTrait, MutFnWithCSTrait, VBox};

verus! {
    spec fn init_prepare_e820_ensures(
        prev_mparam: MonitorParams,
        mparam: MonitorParams,
        cc: SnpCoreConsole,
        ret: &[E820Entry]) -> bool {
        let prev_e820 = prev_mparam.e820();
        let e820 = ret@;
        &&& e820.to_valid_ranges()
            === prev_e820.to_valid_ranges()
        &&& ret@.to_aligned_ranges()
            === prev_e820.to_aligned_ranges()
        &&& mparam === prev_mparam.spec_set_validated_e820(mparam.validated_e820)
                                .spec_set_validated_entries(mparam.validated_entries)
        &&& mparam.validated_entries.spec_eq(ret@.len())
        &&& format_range_ensures(
            ret@,
            prev_mparam.validated_e820@.take(prev_mparam.validated_entries.vspec_cast_to()),
            prev_mparam.validated_entries.vspec_cast_to()
        )
        &&& ret@.is_constant()
        &&& ret@ === mparam.e820()
        &&& cc.wf()
        &&& mparam.is_constant()
    }

    pub struct InitE820Fn;
    pub type InitE820Params = InitE820Fn;
    pub type InitE820Out<'a> = (&'a [E820Entry]);
    impl<'a> MutFnWithCSTrait<'a, SnpCoreConsole, InitE820Fn, InitE820Out<'a>> for MonitorParams {
        closed spec fn spec_update_cs_requires(&self, params: InitE820Fn, cs: SnpCoreConsole) -> bool {
            &&& self.is_constant()
            &&& cs.wf()
        }
        closed spec fn spec_update_cs(&self, prev: &Self, params: InitE820Fn, oldcs: SnpCoreConsole, ret: InitE820Out<'a>, cs: SnpCoreConsole) -> bool {
            &&& init_prepare_e820_ensures(*prev, *self, cs, ret)
            &&& cs.wf_core(oldcs.snpcore.cpu())
            &&& cs.snpcore.only_reg_coremode_updated(
                oldcs.snpcore,
                set![GHCB_REGID()])
        }
        fn box_update_cs(
            &'a mut self,
            params: InitE820Fn, Tracked(cc): Tracked<&mut SnpCoreConsole>) -> (ret: InitE820Out<'a>)
        {
            let e820_entries = self.validated_entries.into();
            if (e820_entries >= ValidatedE820Table::const_len()) || (e820_entries == 0) {
                // Wrong e820 size
                new_strlit("Invalid e820 size\n").leak_debug();
                early_vc_terminate_debug(SM_TERM_INVALID_PARAM, Tracked(cc));
            }

            let ghost prev_e820 = self.validated_e820@.take(e820_entries as int);
            self.validated_e820.leak_debug();
            let e820 = e820_format(&mut self.validated_e820, e820_entries);
            if e820.is_none() {
                new_strlit("e820 format err\n").leak_debug();
                early_vc_terminate_debug(SM_TERM_INVALID_PARAM, Tracked(cc));
            }
            let e820 = e820.unwrap();
            self.validated_entries = e820.len().into();
            proof {
                assert(e820@.to_valid_ranges() === prev_e820.to_valid_ranges());
                assert(e820@.to_aligned_ranges() =~~= prev_e820.to_aligned_ranges()) by {
                    e820@.lemma_align_ranges_reveal();
                    e820@.lemma_valid_ranges_reveal();
                    prev_e820.lemma_align_ranges_reveal();
                    prev_e820.lemma_valid_ranges_reveal();
                    assert(e820@.to_valid_ranges_internal() =~~= prev_e820.to_valid_ranges_internal());
                    assert(e820@.to_aligned_ranges_internal2() =~~= prev_e820.to_aligned_ranges_internal2());
                }
            }
            e820
        }
    }
    pub struct InitCpuCount;
    type InitCpuCountParams = (InitCpuCount, u64_s);
    impl<'a> MutFnTrait<'a, InitCpuCountParams, u64_s> for MonitorParams {
        closed spec fn spec_update_requires(&self, params: InitCpuCountParams) -> bool {
            &&& self.is_constant()
        }
        closed spec fn spec_update(&self, prev: &Self, params: InitCpuCountParams, ret: u64_s) -> bool {
            *self === prev.spec_set_cpu_count(params.1)
        }
        fn box_update(
            &'a mut self,
            params: InitCpuCountParams) -> (ret: u64_s)
        {
            self.cpu_count = params.1;
            params.1
        }
    }

    pub fn init_mem(
        mp_ptr: SnpPPtr<MonitorParams>,
        Tracked(mp_perms): Tracked<MonitorParamPerms>,
        Tracked(alloc_perm): Tracked<SnpPointsTo<VeriSMoAllocator>>,
        Tracked(alloc_lock): Tracked<&mut LockPermRaw>,
        Tracked(memcc): Tracked<SnpMemCoreConsole>,
        Tracked(unused_preval_memperm): Tracked<RawMemPerms>) ->
        (ret: (VBox<MonitorParams>, VBox<OnePage>, Tracked<SnpCoreConsole>, Tracked<MonitorParamGlobalPerms>))
    requires
        memcc.memperm.mem_perms_e820_invalid(mp_perms@.e820()),
        memcc.wf(),
        unused_preval_memperm.mem_perms_e820_valid(mp_perms@.e820()),
        unused_preval_memperm.wf(),
        mp_perms@.wf_at(mp_ptr),
        mp_ptr.is_constant(),
        is_alloc_perm(alloc_perm@),
        old(alloc_lock)@.is_clean_lock_for(
            spec_ALLOCATOR_range(),
            memcc.cc.snpcore.cpu()
        )
    ensures
        ret.2@.wf_core(memcc.cc.snpcore.cpu()),
        ret.3@.wf_value(ret.0@),
        spec_ALLOCATOR().lock_default_mem_requires(
            ret.2@.snpcore.cpu(), alloc_lock@),
        is_permof_ALLOCATOR(alloc_lock@),
        ret.2@.snpcore.only_reg_coremode_updated(
            memcc.cc.snpcore,
            set![GHCB_REGID()]),
        ret.0@.mp_wf(),
        ret.0.snp() === SwSnpMemAttr::spec_default(),
    {
        let tracked mut memcc = memcc;
        let tracked mut mp_perms = mp_perms;
        let tracked SnpMemCoreConsole {memperm, cc} = memcc;
        let start_addr = verismo_start_addr();
        let end_addr = verismo_end_addr();

        proof {
            reveal_strlit("\nwelcome verismo:\n");
        }
        new_strlit("\nwelcome verismo:\n").info(Tracked(&mut cc));
        if !start_addr.check_valid_addr(1) ||
            !end_addr.check_valid_addr(0) ||
            start_addr >= end_addr {
            // bad address
            new_strlit("bad address\n").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }

        let start = start_addr.to_page();
        let end = page_align_up(end_addr).to_page();

        if !mp_ptr.check_valid() {
            // Wrong pointer value
            new_strlit("bad mp_ptr\n").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }

        let tracked MonitorParamPerms {
            mp: mpraw_perm,
            hvparampage: hvraw_perm,
            global_perms,
        } = mp_perms;
        let tracked mut mp_perm = mpraw_perm.tracked_into();
        proof {
            let N: nat = 16;
            assert(N == 16 ==> N * spec_size::<u8_s>() == 16 * spec_size::<u8_s>());
            let N: nat = 0x80;
            assert(N == 0x80 ==> N * spec_size::<HyperVMemMapEntry>() == 0x80 * spec_size::<HyperVMemMapEntry>());
            assert(spec_size::<HvParamTable>() < PAGE_SIZE!());
        };
        let tracked (hvparam_perm, hv_unused) = hvraw_perm.trusted_split(spec_size::<HvParamTable>());
        let tracked mut hvparam_perm: SnpPointsTo<HvParamTable> = hvparam_perm.tracked_into();
        let mparam = mp_ptr.borrow(Tracked(&mp_perm));

        if !mparam.check_valid() {
            new_strlit("\nInvalid mparam\n").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }

        #[cfg(debug_assertions)]{
        let mparam2 = SimpleMonitorParams{
            cpuid_page: mparam.cpuid_page,         // cpuid page gpa
            secret_page: mparam.secret_page, // secret page gpa
            hv_param: mparam.hv_param,            // param page gpa
            validated_entries: mparam.validated_entries,
            acpi: mparam.acpi,
            acpi_size: mparam.acpi_size,
            richos_start: mparam.richos_start,
            richos_size: mparam.richos_size,
            richos_cmdline_len: mparam.richos_cmdline_len,
        };
        // Output parameters for debugging purpose.
        mparam2.debug(Tracked(&mut cc));
        }
        let hv_addr: usize = mparam.hv_param.into();
        let hvparam_ptr: SnpPPtr<HvParamTable> = SnpPPtr::from_usize(hv_addr);

        if !hvparam_ptr.check_valid() {
            new_strlit("bad hvparam_ptr\n").leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cc.snpcore));
        }
        let mut mparam = VBox::from_raw(mp_ptr.to_usize(), Tracked(mp_perm));
        proof{
        assert(mparam@.mp_wf());
        assert(mparam.wf());
        }
        let mut hvparam: VBox<HvParamTable> = VBox::from_raw(hvparam_ptr.to_usize(), Tracked(hvparam_perm));
        assert(hvparam.wf());
        mparam.box_update((InitCpuCount, hvparam.borrow().cpu_count));
        // format e820 params
        let e820 = mparam.box_update_cs(InitE820Fn, Tracked(&mut cc));
        SlicePrinter{s: e820}.debug(Tracked(&mut cc));
        // format hv params
        let (hv_mem_slice) = hvparam.box_update_cs(
            FmtHvParamCall, Tracked(&mut cc));
        let cc = process_vm_mem(hv_mem_slice, e820, start_addr, end_addr,
            Tracked(SnpMemCoreConsole {memperm, cc}),
            Tracked(unused_preval_memperm),
            Tracked(alloc_perm), Tracked(alloc_lock));
        let (_, Tracked(hvparam_perm)) = hvparam.into_raw();
        let tracked hvraw_perm = hvparam_perm.tracked_into_raw().trusted_join(hv_unused);
        (mparam, VBox::from_raw(hvparam_ptr.to_usize(), Tracked(hvraw_perm.tracked_into())), cc, Tracked(global_perms))
    }
}

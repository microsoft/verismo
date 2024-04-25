use super::*;
use crate::security::SnpSecretsPageLayout;
use crate::snp::cpu::{InitAPParams, InitApVmsa, PerCpuData, GDT};
use crate::snp::percpu::BSP;
use crate::pgtable_e::va_to_pa;

verus! {

impl GhcbHyperPageHandle {
    /*
    EnableVtlProtection      : 0xb0;
    DefaultVtlProtectionMask : 0xb1111;
    ZeroMemoryOnReset        : 0xb0;
    DenyLowerVtlStartup      : 0xb0;
    InterceptAcceptance      : 1;
    InterceptEnableVtlProtection : 0;
    InterceptVpStartup       : 0;
    InterceptCpuidUnimplemented : 0;
    InterceptUnrecoverableException : 1;
    InterceptPage            : 0;
    InterceptRestorePartitionTime : 0;
    InterceptNotPresent      : 0;
    ReservedZ                : 0 */
    pub fn config_partition(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (handle: Self)
        requires
            self.wf(),
            (*old(cs)).inv(),
        ensures
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
            handle.wf(),
    {
        let ghost cs1 = (*cs);
        let handle = self.set_vp_reg(
            HV_REGISTER_VSM_PARTITION_CONFIG,
            0x89e,
            REG_NO_USE_VTL,
            Tracked(cs),
        );
        let ghost cs2 = (*cs);
        let (val, handle) = handle.get_vp_reg(
            HV_REGISTER_VSM_PARTITION_CONFIG,
            REG_NO_USE_VTL,
            Tracked(cs),
        );
        if val != 0x89e {
            (new_strlit("partition config = "), val).leak_debug();
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
        }
        proof {
            cs1.lemma_update_prop(cs2, (*cs), set![], set![], set![], set![]);
        }
        handle
    }

    fn config_percpu_intercept(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (handle: Self)
        requires
            self.wf(),
            (*old(cs)).inv(),
        ensures
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
            handle.wf(),
    {
        // set restricted interrupt policy at vtl0 0-3: max_vtl, 4-5: vtl0_int, 6-7: vtl1_int
        let ghost oldcs = (*cs);
        let (mut val, handle) = self.get_vp_reg(
            HV_REGISTER_GUEST_VSM_PARTITION_CONFIG,
            REG_NO_USE_VTL,
            Tracked(cs),
        );
        let ghost prevcs = (*cs);
        val = (val & 0xffff_ffff_ffff_ffcfu64) | 0x10u64;
        let handle = handle.set_vp_reg(
            HV_REGISTER_GUEST_VSM_PARTITION_CONFIG,
            val,
            REG_NO_USE_VTL,
            Tracked(cs),
        );
        proof {
            oldcs.lemma_update_prop(prevcs, (*cs), set![], set![], set![], set![]);
        }
        handle
    }

    pub fn register_vmsa(
        self,
        vmpl: u8,
        vmsa: VBox<VmsaPage>,
        Tracked(nextvmpl_id): Tracked<CoreIdPerm>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (Self, VBox<VmsaPage>))
        requires
            self.wf(),
            (*old(cs)).inv(),
            vmsa.is_vmpl0_private_page(),
            vmsa@.vmpl.spec_eq(vmpl as int),
            nextvmpl_id@.vmpl == vmpl,
            0 < vmpl < 4,
        ensures
            cs.inv(),
            cs.only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
            ret.0.wf(),
            ret.1.is_vmsa_page(),
            ret.1@ === vmsa@,
    {
        // install intercept
        new_strlit("Register page.").leak_debug();
        let ghost cs1 = (*cs);
        let GhcbHyperPageHandle(ghcb, hyperpage) = self;
        let ghcb = ghcb.ghcb_write_msr(HV_X64_MSR_SINT0, KeX64VectorSintIntercept, Tracked(cs));
        let ghost cs2 = (*cs);
        let handle = GhcbHyperPageHandle(ghcb, hyperpage);
        let vmsa_addr = vmsa.get_const_addr() as u64;
        proof {
            proof_cast_from_seq_unique(vmsa@);
        }
        let (vmsa_ptr, Tracked(vmsa_perm)) = vmsa.into_raw();
        let tracked mut vmsa_perm = vmsa_perm.tracked_into_raw();
        // register vmsa

        let vmsa_paddr = va_to_pa(vmsa_addr, Tracked(&vmsa_perm));
        let value = (vmsa_paddr as u64) | HV_X64_REGISTER_SEV_CONTROL_USE_SEV;
        let handle = handle.set_vp_reg(
            HV_X64_REGISTER_SEV_CONTROL,
            value,
            REG_USE_VTL | get_vtl(vmpl),
            Tracked(cs),
        );
        let ghost cs3 = (*cs);
        let rmp_attr = RmpAttr::empty().set_vmpl(vmpl as u64).set_vmsa(1).set_perms(0);
        assert(crate::arch::rmp::PagePerm::from_int(0) =~~= Set::empty());
        proof {
            let vmsa: VmsaPage = vmsa_perm@.bytes().vspec_cast_to();
            let vmpl = vmsa.vmpl;
            assert(vmpl.spec_eq(nextvmpl_id@.vmpl));
            assert(vmsa_perm@.snp().requires_rmpadjust_mem(
                vmsa_addr as int,
                0,
                rmp_attr@,
                Some(nextvmpl_id),
            ));
        }
        assert(vmsa_perm@.wf());
        let rc = rmpadjust(
            vmsa_addr,
            RMP_4K,
            rmp_attr,
            Tracked(&cs.snpcore),
            Tracked(Some(nextvmpl_id)),
            Tracked(&mut vmsa_perm),
        );
        if rc != 0 {
            // failed validation ==> possible attack
            vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
        }
        assert(vmsa_perm@.wf());
        let handle = handle.config_percpu_intercept(Tracked(cs));
        proof {
            cs1.lemma_update_prop(cs2, cs3, set![], set![], set![], set![]);
            cs1.lemma_update_prop(cs3, (*cs), set![], set![], set![], set![]);
        }
        assert(spec_size::<VmsaPage>() == PAGE_SIZE!());
        (handle, VBox::from_raw((vmsa_addr as usize), Tracked(vmsa_perm.tracked_into())))
    }

    pub fn snp_start_ap(
        self,
        cpu: VBox<PerCpuData>,
        gdt: &GDT,
        Tracked(ap_id): Tracked<CoreIdPerm>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (handle: Self)
        requires
            self.wf(),
            old(cs).inv(),
            ap_id@.vmpl == 0,
            cpu@.cpu != BSP,
            cpu@.inv(),
            cpu.wf(),
            gdt.is_constant(),
            cpu.snp() === SwSnpMemAttr::spec_default(),
        ensures
            cs.inv(),
            cs.only_lock_reg_coremode_updated(
                *old(cs),
                set![],
                set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
            ),
            handle.wf(),
    {
        let ghost cs1 = *cs;
        let GhcbHyperPageHandle(bsp_ghcb_h, bsp_hyperpage_h) = self;
        let cpu_id = cpu.borrow().cpu;
        let mut vmsabox = VBox::<VmsaPage>::new_aligned_uninit(PAGE_SIZE, Tracked(cs));
        proof {
            assert(cs.inv_ac());
            assert(gdt.is_constant());
        }
        let ghost cs2 = *cs;
        vmsabox.box_update_cs(InitAPParams { fun: InitApVmsa, cpu, gdt }, Tracked(cs));
        let ghost cs3 = *cs;
        let (vmsa_ptr, Tracked(vmsa_perm)) = vmsabox.into_raw();
        let vmsa_vaddr = vmsa_ptr.as_u64();
        let tracked mut vmsa_perm = vmsa_perm.tracked_into_raw();
        let vmsa_paddr = va_to_pa(vmsa_vaddr, Tracked(&vmsa_perm));
        new_strlit("Wakeup ").leak_debug();
        // Setup hyperpage and enable VP
        let (ap_hyperv_h, bsp_ghcb_h) = VBox::<OnePage>::new_shared_page(
            PAGE_SIZE,
            bsp_ghcb_h,
            Tracked(cs),
        );
        let ghost cs4 = (*cs);
        // Enable VTL for the VP
        let (ap_hyperv_ptr, Tracked(ap_hyperv_perm)) = ap_hyperv_h.into_raw();
        let input = HvCallVpVtlInput::new(HV_PARTITION_ID_SELF, cpu_id, get_vtl(0), vmsa_paddr);
        let input_ptr: SnpPPtr<HvCallVpVtlInput> = ap_hyperv_ptr.to();
        let (_, Tracked(ap_hyperv_perm)) = input_ptr.replace_with::<OnePage>(
            input,
            Tracked(ap_hyperv_perm),
        );
        let ap_hyperv_h = HyperPageHandle::from_raw(
            ap_hyperv_ptr.to_usize(),
            Tracked(ap_hyperv_perm),
        );
        let bsp_for_ap_handle = GhcbHyperPageHandle(bsp_ghcb_h, ap_hyperv_h);
        let (ret, bsp_for_ap_handle) = bsp_for_ap_handle.hv_call_with_retry(
            hvcall_code(HVCALL_ENABLE_VP_VTL, 0),
            true,
            false,
            Tracked(cs),
        );
        let ghost cs5 = (*cs);
        match ret {
            Ok(status) if status != 0 => {
                (new_strlit("Failed"), status).leak_debug();
            },
            Err(code) => {
                vc_terminate_debug(SM_TERM_VMM_ERR, Tracked(cs));
            },
            _ => {},
        }
        // rmpadjust vmsa page to be a real vmsa page.
        // VMPL > 0 but is ignored when set vmsa.

        let mut rmp_attr = RmpAttr::empty().set_vmpl(VMPL::VMPL1.as_u64()).set_vmsa(1).set_perms(0);
        let rc = rmpadjust(
            vmsa_vaddr,
            0,
            rmp_attr,
            Tracked(&mut cs.snpcore),
            Tracked(Some(ap_id)),
            Tracked(&mut vmsa_perm),
        );
        if rc != 0 {
            vc_terminate(SM_TERM_VMM_ERR, Tracked(&mut cs.snpcore));
        }
        // Ask hypervisor to wakeup the processor.

        let (ret, bsp_for_ap_handle) = bsp_for_ap_handle.hv_call_with_retry(
            hvcall_code(HVCALL_START_VIRTUAL_PROCESSOR, 0),
            true,
            false,
            Tracked(cs),
        );
        match ret {
            Ok(status) if status == 0 => {
                (new_strlit("Boot AP"), cpu_id).leak_debug();
            },
            _ => {
                vc_terminate(SM_TERM_VMM_ERR, Tracked(&mut cs.snpcore));
            },
        }
        proof {
            assert(set![spec_ALLOCATOR_lockid()].union(set![spec_ALLOCATOR_lockid()])
                =~~= set![spec_ALLOCATOR_lockid()]);
            cs1.lemma_update_prop(
                cs2,
                cs3,
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_ALLOCATOR_lockid()],
            );
            cs1.lemma_update_prop(
                cs3,
                cs4,
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_ALLOCATOR_lockid()],
            );
            cs1.lemma_update_prop(
                cs4,
                cs5,
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_PT_lockid()],
            );
            assert(set![spec_ALLOCATOR_lockid()].union(set![spec_PT_lockid()])
                =~~= set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
            cs1.lemma_update_prop(
                cs5,
                *cs,
                set![],
                set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                set![],
                set![],
            );
        }
        let GhcbHyperPageHandle(bsp_ghcb_h, ap_hyperv_h) = bsp_for_ap_handle;
        ap_hyperv_h.into_raw();  // TODO: pass to ap vmsa.
        GhcbHyperPageHandle(bsp_ghcb_h, bsp_hyperpage_h)
    }

    pub fn start_all_ap(
        self,
        cpu_count: u32,
        secret: &SnpSecretsPageLayout,
        gdt: &GDT,
        Tracked(ap_ids): Tracked<Map<int, CoreIdPerm>>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (handle: Self)
        requires
            self.wf(),
            (*old(cs)).inv(),
            spec_ap_ids_wf(ap_ids, BSP as int),
            secret.wf_mastersecret(),
            gdt.is_constant(),
        ensures
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated(
                (*old(cs)),
                set![],
                set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
            ),
            handle.wf(),
    {
        if cpu_count <= 1 {
            return self;
        }
        let ghost oldcs = (*cs);
        let tracked mut ap_ids = ap_ids;
        let mut cpu = 0;
        let mut handle = self;
        while cpu < cpu_count
            invariant
                cs.inv(),
                cs.only_lock_reg_coremode_updated(
                    oldcs,
                    set![],
                    set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                ),
                handle.wf(),
                spec_ap_ids_wf_lowerbound(ap_ids, BSP as int, cpu as int),
                secret.wf_mastersecret(),
                gdt.is_constant(),
        {
            if cpu != BSP as u32 {
                proof {
                    assert(spec_cpumap_contains_cpu(ap_ids, cpu as int, 0));
                }
                let ghost cs1 = (*cs);
                let ghost prev_ap_ids = ap_ids;
                let tracked ap_id = ap_ids.tracked_remove(cpu as int);
                let percpu = VBox::new(PerCpuData { cpu, resvd: 0, secret }, Tracked(cs));
                let ghost cs2 = (*cs);
                handle = handle.snp_start_ap(percpu, gdt, Tracked(ap_id), Tracked(cs));
                proof {
                    oldcs.lemma_update_prop(
                        cs1,
                        cs2,
                        set![],
                        set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                        set![],
                        set![spec_ALLOCATOR_lockid()],
                    );
                    assert(set![spec_ALLOCATOR_lockid(), spec_PT_lockid()].union(
                        set![spec_ALLOCATOR_lockid()],
                    ) =~~= set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
                    oldcs.lemma_update_prop(
                        cs2,
                        (*cs),
                        set![],
                        set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                        set![],
                        set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                    );
                    assert(set![spec_ALLOCATOR_lockid(), spec_PT_lockid()].union(
                        set![spec_ALLOCATOR_lockid(), spec_PT_lockid()],
                    ) =~~= set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
                    assert forall|i: int|
                        (i != BSP) && i >= (cpu + 1) implies spec_cpumap_contains_cpu(
                        ap_ids,
                        i,
                        0,
                    ) by {
                        assert(spec_cpumap_contains_cpu(prev_ap_ids, i, 0));
                    }
                }
            }
            cpu = cpu + 1;
        }
        handle
    }
}

impl GhcbHandle {
    // Ask hypervisor to switch to a lower VTL
    pub fn switch_to_next_vmpl(
        self,
        vmsa: VBox<VmsaPage>,
        Tracked(snpcore): Tracked<&mut SnpCore>,
    ) -> (ret: (Self, VBox<VmsaPage>))
        requires
            self.ghcb_wf(),
            vmsa.is_vmsa_page(),
            (*old(snpcore)).inv(),
        ensures
            (*snpcore).inv(),
            (*snpcore).only_reg_coremode_updated((*old(snpcore)), set![GHCB_REGID()]),
            ret.0.ghcb_wf(),
            ret.1.only_val_updated(vmsa),
            ret.1.is_vmsa_page(),
    {
        let error_mask: u64 = 0xfff;
        let mut ghcb = self;
        let mut vmsa = vmsa;
        let ghost oldvmsa = vmsa;
        vmsa.set_guest_error_code(error_mask.into());
        let vmsa = vmsa;
        assert(vmsa.only_val_updated(oldvmsa));
        let ghost oldsnpcore = *snpcore;
        loop
            invariant
                ghcb.ghcb_wf(),
                snpcore.inv(),
                snpcore.only_reg_coremode_updated(oldsnpcore, set![GHCB_REGID()]),
                vmsa.is_vmsa_page(),
            ensures
                ghcb.ghcb_wf(),
                snpcore.inv(),
                snpcore.only_reg_coremode_updated(oldsnpcore, set![GHCB_REGID()]),
                vmsa.is_vmsa_page(),
        {
            let mut check_error = vmsa.copy_guest_error_code();
            check_error.declassify();
            if error_mask != check_error.reveal_value() {
                break ;
            }
            ghcb.box_update(GhcbClear);
            let ghost prev_ghcb = ghcb@;
            ghcb.set_usage_ext(GHCB_VTL_RETURN_USAGE.into());
            assert(ghcb.ghcb_wf());
            let (ghcb_ptr, Tracked(mut ghcbpage_perm)) = ghcb.into_raw();
            assert(ghcbpage_perm@.snp() === SwSnpMemAttr::shared()) by {
                ghcb.proof_ghcb_wf();
            }
            let tracked mut ghcb_msr_perm = snpcore.regs.tracked_remove(GHCB_REGID());
            let tracked mut op_ghcbpage_perm = Some(ghcbpage_perm.tracked_into_raw());
            vmgexit(
                Tracked(&mut ghcb_msr_perm),
                Tracked(&mut snpcore.coreid),
                Tracked(&mut op_ghcbpage_perm),
            );
            let tracked ghcbpage_perm = op_ghcbpage_perm.tracked_unwrap().tracked_into();
            ghcb = VBox::from_raw(ghcb_ptr.to_usize(), Tracked(ghcbpage_perm));
            proof {
                snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
            }
        }
        (ghcb, vmsa)
    }
}

} // verus!

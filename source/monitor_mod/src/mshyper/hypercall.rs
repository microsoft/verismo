use super::*;

verus! {
impl GhcbHyperPageHandle {
    // ret.0: Ok(hypercall status) if GHCB call succeeds; else GHCB error code
    pub fn hv_call(self, control: u64, has_input: bool, has_output: bool,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: (Result<HvCallStatus, SvmStatus>, GhcbHyperPageHandle))
    requires
        self.wf(),
        (*old(cs)).inv(),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
        ret.1.wf(),
    {
        let ret = SvmStatus::Ok;
        let GhcbHyperPageHandle(mut ghcb, mut hyperpage) = self;
        let hyperpage_addr: u64 = hyperpage.get_const_addr() as u64;
        let in_addr = if has_input {hyperpage_addr} else{0};
        let out_addr = if has_output {hyperpage_addr} else{0};
        assert(ghcb.ghcb_wf());
        ghcb.box_update(GhcbClear);
        assert(ghcb.ghcb_wf());
        ghcb.box_update((GhcbSetCplFn, 0));
        ghcb.box_update((GhcbSetRaxFn, 0));
        ghcb.box_update((GhcbSetRcxFn, control));
        ghcb.box_update((GhcbSetRdxFn, in_addr)); // input addr
        ghcb.box_update((GhcbSetR8Fn, out_addr)); // output addr
        let mut exit_code = SVM_EXIT_VMMCALL;
        let mut exit_info1 = 0;
        let mut exit_info2 = 0;
        let (resp, mut ghcb) = ghcb.ghcb_page_proto(
            &mut exit_code,
            &mut exit_info1,
            &mut exit_info2,
            Tracked(cs),
        );
        // Cannot borrow Hv-shared memory. Copy to private.
        let ret: Result<HvCallStatus, SvmStatus> = match resp {
            SvmStatus::Ok => {
                if ghcb.box_borrow(GhcbCheckRax) {
                    let (rax, newghcb) = ghcb.rax();
                    ghcb = newghcb;
                    Ok(rax)
                } else {
                    new_strlit("resp rax is invalid").leak_debug();
                    Err(SvmStatus::VmmError)
                }
            },
            _ => Err(ret),
        };
        (ret, GhcbHyperPageHandle(ghcb, hyperpage))
    }

    pub fn hv_call_with_retry(
        self, control: u64, has_input: bool, has_output: bool,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>
    ) -> (ret: (Result<HvCallStatus, SvmStatus>, GhcbHyperPageHandle))
    requires
        self.wf(),
        (*old(cs)).inv(),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
        ret.1.wf(),
    {
        (new_strlit("hvcall start: "), control).leak_debug();
        let mut i = 0;
        let mut ret: Result<HvCallStatus, SvmStatus> = Err(SvmStatus::Unsupported);
        let mut handle = self;
        let ghost oldcs = (*cs);
        while i < HV_MAX_RETRY
        invariant
            0 <= i <= HV_MAX_RETRY,
            handle.wf(),
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated(oldcs, set![], set![]),
        ensures
            handle.wf(),
            (*cs).inv(),
            (*cs).only_lock_reg_coremode_updated(oldcs, set![], set![]),
        {
            let ghost prevcs = (*cs);
            let (tmpret, tmphandle) = handle.hv_call(control, has_input, has_output, Tracked(cs));
            proof{
                oldcs.lemma_update_prop(prevcs, (*cs), set![], set![], set![], set![]);
            }
            ret = tmpret;
            handle = tmphandle;
            i = i + 1;
            match &ret {
                Ok(hvcall_code) => {
                    let hvcall_code = (*hvcall_code) as u32 as u64;
                    ((new_strlit("status: "), hvcall_code), new_strlit("\n")).leak_debug();
                    if hvcall_code != HV_STATUS_TIMEOUT {
                        break;
                    }
                    continue;
                }
                Err(code) => {
                    (new_strlit("err: "), code.as_u64()).leak_debug();
                    break;
                }
            }
        }
        (ret, handle)
    }

    //pub const USE_VTL: u8 = 0x10;
    /// Set VP register
    /// HVCALL_SET_VP_REGISTERS
    ///  vtl[0:4]: vtl value
    ///  vtl[5]: use vtl
    pub fn set_vp_reg(self, reg: u32, val: u64, use_vtl: u8,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>) ->
    (handle: Self)
    requires
        self.wf(),
        (*old(cs)).inv(),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
        handle.wf(),
    {
        ((new_strlit("set_vp_reg:"), reg), val).leak_debug();
        let control = hvcall_code(HVCALL_SET_VP_REGISTERS, 1);
        let reserved = Array::new(u8_s::new(0));
        let input = HvCallInputSetReg {
            ptid: HV_PARTITION_ID_SELF.into(),
            vpid: HV_VP_INDEX_SELF.into(),
            element: RegSetEntry {
                name: reg.into(),
                value_low: val.into(),
                value_high: (0u64).into(),
                reserved_2: 0u32.into(),
                reserved_3: 0u64.into(),
            },
            vtl: use_vtl.into(),
            reserved,
        };
        let GhcbHyperPageHandle(mut ghcb, mut hyperpage) = self;
        let (hyper_ptr, Tracked(hyperperm)) = hyperpage.into_raw();
        let input_ptr = hyper_ptr.to();
        let (_, Tracked(hyperperm)) = input_ptr.replace_with::<OnePage>(input, Tracked(hyperperm));
        let hyperpage = VBox::from_raw(hyper_ptr.to_usize(), Tracked(hyperperm));
        let mut handle = GhcbHyperPageHandle(ghcb, hyperpage);
        let (status, handle) = handle.hv_call_with_retry(control, true, false, Tracked(cs));
        match status {
            Ok(hvcall_code) if (hvcall_code as u32)!= 0 => {
                vc_terminate(SM_TERM_VMM_ERR,
                    Tracked(&mut cs.snpcore));
            }
            _ => {}
        }
        handle
    }

    pub fn get_vp_reg(self, reg: u32, use_vtl: u8,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>) ->
    (ret_handle: (u64, Self))
    requires
        self.wf(),
        (*old(cs)).inv(),
    ensures
        (*cs).inv(),
        (*cs).only_lock_reg_coremode_updated((*old(cs)), set![], set![]),
        ret_handle.1.wf(),
    {

        let control = hvcall_code(HVCALL_GET_VP_REGISTERS, 1);
        let reserved = Array::new(u8_s::new(0));
        let input = HvCallInputGetReg {
            ptid: HV_PARTITION_ID_SELF.into(),
            vpid: HV_VP_INDEX_SELF.into(),
            element: RegGetEntry {
                name0: reg.into(),
                name1: 0u32.into(),
            },
            vtl: use_vtl.into(),
            reserved,
        };
        let GhcbHyperPageHandle(mut ghcb, mut hyperpage) = self;
        let (hyper_ptr, Tracked(hyperperm)) = hyperpage.into_raw();
        let input_ptr = hyper_ptr.to();
        let (_, Tracked(hyperperm)) = input_ptr.replace_with::<OnePage>(input, Tracked(hyperperm));
        let hyperpage = VBox::from_raw(hyper_ptr.to_usize(), Tracked(hyperperm));
        let mut handle = GhcbHyperPageHandle(ghcb, hyperpage);
        let (status, handle) = handle.hv_call_with_retry(control, true, true, Tracked(cs));
        match status {
            Ok(hvcall_code) if hvcall_code as u32 != 0 => {
                vc_terminate(SM_TERM_VMM_ERR,
                    Tracked(&mut cs.snpcore));
            }
            _ => {}
        }
        let GhcbHyperPageHandle(ghcb, hyperpage) = handle;
        let (hyper_ptr, Tracked(hyperperm)) = hyperpage.into_raw();
        let output_ptr = hyper_ptr.to::<HvCallOutputGetReg>();
        let (output, Tracked(hyperperm)) = output_ptr.copy_with::<OnePage>(Tracked(hyperperm));
        let hyperpage = VBox::from_raw(hyper_ptr.to_usize(), Tracked(hyperperm));
        (output.low.into(), GhcbHyperPageHandle(ghcb, hyperpage))
    }
}
}

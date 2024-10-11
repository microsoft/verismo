use super::*;
use crate::arch::reg::MSR_GHCB_BASE;
use crate::debug::VPrintAtLevel;
use crate::registers::*;

verus! {

#[inline]
pub fn SM_EVERCRYPT_ERR(subcode: u64_t) -> (ret: u64_t)
    requires
        subcode < 0x100,
{
    proof {
        assert(subcode << 8 < 0x10000) by (bit_vector)
            requires
                subcode < 0x100,
        ;
    }
    (SM_EVERCRYPT_EXIT + (subcode << SUBCODE_OFFSET))
}

#[inline]
pub fn SM_TERM_RICHOS_ERR(subcode: u64_t) -> (ret: u64_t)
    requires
        subcode < 0x100,
{
    proof {
        assert(subcode << 0x8 < 0x10000) by (bit_vector)
            requires
                subcode < 0x100,
        ;
    }
    (SM_TERM_RICHOS + (subcode << SUBCODE_OFFSET))
}

} // verus!
verus! {

pub const GHCB_HV_DEBUG: u64 = 0xf03;

} // verus!
/*
#[verifier::external]
pub mod trust {
    use alloc::fmt;

    use super::*;
    impl fmt::Write for GHCBProto {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            GHCBProto::print_str(s);
            Ok(())
        }
    }
}*/
verus! {

pub open spec fn GHCB_REGID() -> RegName {
    RegName::MSR(MSR_GHCB_BASE)
}

} // verus!
verismo! {
    pub const fn MSR_GHCB() -> (ret: Msr)
    ensures
        ret.reg_id() === GHCB_REGID()
    {
        Msr {
            reg: u32_s::constant(MSR_GHCB_BASE),
        }
    }
}

verus! {

impl GHCBProto {
    #[inline]
    pub fn exit_value(reason_code: u64) -> (ret: u64)
        ensures
            ret == GHCBProto::spec_exit_value(reason_code as u64),
    {
        let mut value: u64 = GHCB_MSR_TERMINATE_REQ;
        value = value | (SM_SEV_TERM_SET << 12u64);
        value = value | (reason_code << 16u64);
        assert(value == GHCBProto::spec_exit_value(reason_code as u64));
        value
    }

    #[inline]
    fn msr_page_state_change_req(ppage: usize_t, op: PageOps) -> (ret: u64)
        ensures
            (ret as int) == GHCBProto::spec_msr_page_state_req(ppage as usize, op),
    {
        GHCB_SNP_PAGE_STATE_CHANGE_REQ as u64 | (ppage as u64 & 0xfff_ffff_ffff) << 12u64 | (
        op.as_u64() as u64) << 52u64
    }

    #[inline(always)]
    pub fn msr_data(value: u64) -> (ret: u64)
        ensures
            ret == value as u64 & !GHCB_MSR_INFO_MASK,
    {
        value & !GHCB_MSR_INFO_MASK
    }

    #[inline(always)]
    pub fn msr_info(value: u64) -> (ret: u64)
        ensures
            ret == value as u64 & GHCB_MSR_INFO_MASK,
    {
        value & GHCB_MSR_INFO_MASK
    }

    #[inline(always)]
    pub fn msr_register_ghcb(page: u64) -> (ret: u64)
        ensures
            ret == page as u64 | GHCB_MSR_REGISTER_GHCB_REQ,
    {
        page | GHCB_MSR_REGISTER_GHCB_REQ
    }

    pub open spec fn restored_ghcb(new: SnpCore, prev: SnpCore) -> bool {
        !spec_attack() ==> new.regs[GHCB_REGID()].view::<usize_s>().value
            == prev.regs[GHCB_REGID()].view::<usize_s>().value
    }
}

} // verus!
verus! {

pub open spec fn spec_eq_shared(expected: nat, ret: nat) -> bool {
    &&& !spec_attack() ==> expected == ret
}

pub open spec fn spec_ghcb_send_core_update(
    oldsnpcore: SnpCore,
    snpcore: SnpCore,
    req_resp: (nat, nat),
) -> bool {
    &&& snpcore.ghcbmsr_msgs() === oldsnpcore.ghcbmsr_msgs().push(req_resp)
    &&& snpcore.reg_updated(oldsnpcore, set![GHCB_REGID()])
    &&& snpcore.update_reg_coremode(oldsnpcore)
}

pub fn ghcb_msr_send(
    val: u64,
    Tracked(memperm): Tracked<&mut Option<SnpPointsToRaw>>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
) -> (ret: u64)
    requires
        (*old(snpcore)).inv_reg_cpu(),
        val.is_constant(),
        is_none_or_sharedmem(*old(memperm)),
    ensures
        (*snpcore).inv_reg_cpu(),
        spec_ghcb_send_core_update(*old(snpcore), *snpcore, (val as nat, snpcore.last_ghcb_resp())),
        snpcore.regs[GHCB_REGID()].val::<u64_s>()@.val == snpcore.last_ghcb_resp(),
        hvupdate_none_or_sharedmem(*memperm, *old(memperm)),
        ret.is_constant(),
        spec_eq_shared(snpcore.last_ghcb_resp(), ret as nat),
{
    //let tracked SnpCore{regs, coreid} = snpcore;
    let tracked mut ghcbperm = snpcore.regs.tracked_remove(GHCB_REGID());
    let ghcb_msr = MSR_GHCB();
    ghcb_msr.write(val.into(), Tracked(&mut ghcbperm));
    //ghcb_msr.write_vmgexit(val, Tracked(&mut ghcbperm), Tracked(&mut snpcore.coreid), Tracked(memperm));
    proof {
        let ghcb_write_val: nat = ghcbperm.val::<u64_s>().vspec_cast_to();
        assert(ghcb_write_val == val as nat);
    }
    vmgexit(Tracked(&mut ghcbperm), Tracked(&mut snpcore.coreid), Tracked(memperm));
    let ret = ghcb_msr.read(Tracked(&ghcbperm)).reveal_value();
    proof {
        snpcore.regs.tracked_insert(GHCB_REGID(), ghcbperm);
    }
    ret
}

} // verus!
verus! {

pub fn ghcb_proto(
    val: u64,
    Tracked(memperm): Tracked<&mut Option<SnpPointsToRaw>>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
) -> (ret: u64)
    requires
        old(snpcore).inv_reg_cpu(),
        val.is_constant(),
        is_none_or_sharedmem(*old(memperm)),
    ensures
        (*snpcore).inv_reg_cpu(),
        GHCBProto::restored_ghcb(*snpcore, *old(snpcore)),
        spec_ghcb_send_core_update(
            *old(snpcore),
            *snpcore,
            (val as nat, (*snpcore).last_ghcb_resp()),
        ),
        ret.is_constant(),
        spec_eq_shared((*snpcore).last_ghcb_resp(), ret as nat),
        hvupdate_none_or_sharedmem(*memperm, *old(memperm)),
{
    let tracked perm = snpcore.regs.tracked_borrow(GHCB_REGID());
    let ghcb_msr = MSR_GHCB();
    let oldval = ghcb_msr.read(Tracked(perm));
    let ret = ghcb_msr_send(val, Tracked(memperm), Tracked(snpcore));
    let tracked mut perm = snpcore.regs.tracked_remove(GHCB_REGID());
    ghcb_msr.write(oldval, Tracked(&mut perm));
    proof {
        snpcore.regs.tracked_insert(GHCB_REGID(), perm);
    }
    ret
}

} // verus!
verus! {

pub fn ghcb_msr_proto(val: u64, Tracked(snpcore): Tracked<&mut SnpCore>) -> (ret: u64)
    requires
        old(snpcore).inv_reg_cpu(),
        val.is_constant(),
    ensures
        (*snpcore).inv_reg_cpu(),
        GHCBProto::restored_ghcb(*snpcore, *old(snpcore)),
        spec_ghcb_send_core_update(
            *old(snpcore),
            (*snpcore),
            (val as nat, (*snpcore).last_ghcb_resp()),
        ),
        spec_eq_shared((*snpcore).last_ghcb_resp(), ret as nat),
        ret.is_constant(),
{
    let tracked mut nonmem = None;
    ghcb_proto(val, Tracked(&mut nonmem), Tracked(snpcore))
}

} // verus!
verus! {

fn vc_terminate_s(reason_code: u64, Tracked(snpcore): Tracked<&mut SnpCore>) -> (ret: !)
    requires
        (*old(snpcore)).inv_reg_cpu(),
        reason_code.is_constant(),
    ensures
        false,
{
    let value = GHCBProto::exit_value(reason_code);
    ghcb_msr_proto(value, Tracked(snpcore));
    loop {
    }
}

pub fn vc_terminate(reason_code: u64_t, Tracked(snpcore): Tracked<&mut SnpCore>) -> (ret: !)
    requires
        (*old(snpcore)).inv_reg_cpu(),
    ensures
        false,
{
    (new_strlit("terminate: "), reason_code).leak_debug();
    vc_terminate_s(reason_code, Tracked(snpcore))
}

pub fn early_vc_terminate_debug(
    reason_code: u64_t,
    Tracked(cc): Tracked<&mut SnpCoreConsole>,
) -> (ret: !)
    requires
        old(cc).wf(),
    ensures
        false,
{
    vc_terminate_s(reason_code, Tracked(&mut cc.snpcore))
}

pub fn vc_terminate_debug(reason_code: u64_t, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret:
    !)
    requires
        old(cs).inv(),
    ensures
        false,
{
    proof {
        reveal_strlit("terminate: ");
    }
    (new_strlit("terminate: "), reason_code).debug(Tracked(cs));
    vc_terminate_s(reason_code, Tracked(&mut cs.snpcore))
}

// If the previous ghcb message is to request page state change,
// we allow safe update for assigned, asid and page size field in the corresponding page.
#[verifier(external_body)]
proof fn trusted_ghcb_change_page_state(
    tracked perm: &mut SnpPointsToRaw,
    op: PageOps,
    tracked snpcore: &SnpCore,
)
    requires
        snpcore.last_ghcb_req() == GHCBProto::spec_msr_page_state_req(
            old(perm)@.ppage() as usize,
            op,
        ) as nat,
        old(perm)@.range().0 % PAGE_SIZE!() == 0,
        old(perm)@.range().1 == PAGE_SIZE!(),
        old(perm)@.wf(),
    ensures
        perm@.range() === old(perm)@.range(),
        perm@.snp().ensures_rmpupdate(old(perm)@.snp(), op.is_Shared(), op.is_Unsmash()),
        perm@.wf(),
{
}

// the memperm should be mapped to the target physical page.
pub fn ghcb_change_page_state_via_msr(
    ppage: usize_t,
    op: PageOps,
    Tracked(memperm): Tracked<&mut SnpPointsToRaw>,
    Tracked(snpcore): Tracked<&mut SnpCore>,
)
    requires
        old(snpcore).inv_reg_cpu(),
        old(memperm)@.wf(),
        old(memperm)@.range().1 == PAGE_SIZE,
        ppage == old(memperm)@.ppage(),
        old(memperm)@.range().0 % PAGE_SIZE!() == 0,
        ppage.is_constant(),
    ensures
        snpcore.inv_reg_cpu(),
        spec_ghcb_send_core_update(
            *old(snpcore),
            *snpcore,
            (
                GHCBProto::spec_msr_page_state_req(ppage as usize, op) as nat,
                snpcore.last_ghcb_resp(),
            ),
        ),
        ensure_page_perm_change_state(*old(memperm), *memperm, ppage as int, op),
{
    let value = GHCBProto::msr_page_state_change_req(ppage, op);
    let resp = ghcb_msr_proto(value, Tracked(snpcore));
    proof {
        trusted_ghcb_change_page_state(memperm, op, snpcore);
    }
}

pub fn ghcb_register_ghcb(ppage: usize, Tracked(snpcore): Tracked<&mut SnpCore>)
    requires
        old(snpcore).inv_reg_cpu(),
        ppage.is_constant(),
        ppage.spec_valid_pn_with(1),
    ensures
        snpcore.inv_reg_cpu(),
        spec_ghcb_send_core_update(*old(snpcore), *snpcore, snpcore.ghcbmsr_msgs().last()),
        (snpcore.last_ghcb_resp() as u64 & GHCB_MSR_INFO_MASK) != GHCB_MSR_REGISTER_GHCB_RES
            ==> spec_attack(),
        (snpcore.last_ghcb_resp() as u64 & !GHCB_MSR_INFO_MASK) != GVN::new(
            ppage as int,
        ).to_addr().to_u64() ==> spec_attack(),
        snpcore.regs[GHCB_REGID()].val::<u64_s>() === (ppage.spec_to_addr().vspec_cast_to()),
        snpcore.ghcb_value() == ppage.spec_to_addr(),
{
    let pa: u64 = ppage.to_addr() as u64;
    let resp = ghcb_msr_proto(GHCBProto::msr_register_ghcb(pa), Tracked(snpcore));
    // Validate the response
    if GHCBProto::msr_info(resp) != GHCB_MSR_REGISTER_GHCB_RES {
        vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(snpcore));
    }
    if GHCBProto::msr_data(resp) != pa {
        vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(snpcore));
    }
    let tracked mut perm = snpcore.regs.tracked_remove(GHCB_REGID());
    MSR_GHCB().write(pa.into(), Tracked(&mut perm));
    proof {
        snpcore.regs.tracked_insert(GHCB_REGID(), perm);
    }
}

pub fn negotiate_protocol(Tracked(snpcore): Tracked<&mut SnpCore>)
    requires
        old(snpcore).inv_reg_cpu(),
    ensures
        snpcore.inv_reg_cpu(),
        spec_ghcb_send_core_update(
            *old(snpcore),
            *snpcore,
            (GHCB_MSR_SEV_INFO_REQ as nat, snpcore.last_ghcb_resp()),
        ),
        (snpcore.last_ghcb_resp() as u64 & GHCB_MSR_INFO_MASK) != GHCB_MSR_SEV_INFO_RES
            ==> spec_attack(),
        (snpcore).update_reg_coremode(*old(snpcore)),
{
    let resp = ghcb_msr_proto(GHCB_MSR_SEV_INFO_REQ, Tracked(snpcore));
    if GHCBProto::msr_info(resp) != GHCB_MSR_SEV_INFO_RES {
        vc_terminate(SM_TERM_GHCB_RESP_INVALID, Tracked(snpcore));
    }
}

} // verus!

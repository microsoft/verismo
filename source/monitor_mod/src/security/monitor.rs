use alloc::vec::Vec;

use self::mem::osmem_adjust;
use super::*;
use crate::boot::linux::*;
use crate::boot::monitor_params::*;
use crate::debug::VPrint;
use crate::lock::*;
use crate::mshyper::*;
use crate::snp::cpuid::SnpCpuidTable;

pub const MAX_LOCK_REQ: usize = 4;

pub const INVALID_REQ: u64 = 1;

verus! {
    pub fn fill_vec<T>(vec: &mut Vec<Option<T>>, n: usize)
    ensures
        old(vec).len() < n ==> vec.len() == n,
        vec@.subrange(0, old(vec).len() as int) =~~= old(vec)@,
        old(vec).len() >= n ==> *vec === *old(vec),
        forall |i| old(vec).len() <= i < n ==> vec[i] === None,
    {
        if vec.len() >= n {
            return;
        }

        let ghost oldvec = *vec;
        while vec.len() < n
        invariant
            vec.len() <= n,
            vec.len() >= oldvec.len(),
            n >= oldvec.len(),
            forall |i| 0 <= i < oldvec.len() ==> vec[i] === oldvec[i],
            forall |i| oldvec.len() <= i < vec.len() ==> vec[i] === None,
        {
            let ghost prev_vec = *vec;
            vec.push(None);
        }
    }


    fn create_lock_entries(priv_req: &LockKernReq) -> (ret: Vec<(usize, usize)>)
    requires
        priv_req.wf(),
    ensures
        forall |k| 0 <= k < ret.len() ==>
            ret[k].0.spec_valid_pn_with(ret[k].1 as nat),
    {
        let mut entries = Vec::<(usize, usize)>::new();
        let mut i = 0;
        while i < 256
        invariant
            i <= 256,
            entries.len() == i,
            priv_req.wf(),
            forall |k| 0 <= k < i ==> entries[k].0 ===
                    priv_req@[k].start.vspec_cast_to() &&
                    entries[k].1 ==
                        priv_req@[k].end@.val - priv_req@[k].start@.val,
            forall |k| 0 <= k < i ==>
                entries[k].0.spec_valid_pn_with(entries[k].1 as nat),
        {
            let val = priv_req.index(i);
            let mut end = val.end;
            let mut start = val.start;
            end.declassify();
            start.declassify();
            let end: usize = end.into();
            let start: usize = start.into();
            if end <= start || !end.check_valid_pn(0) {
                break;
            }
            entries.push((start, end - start));
            i = i + 1;
        }

        entries
    }
}
verismo_simple! {
#[derive(Copy, VClone)]
pub struct PageRange {
    pub start: u64,
    pub end: u64,
}
}

verus! {
pub const SNP_VMPL_REQ_MAGIC: u64 = 0xfeeddead;

#[derive(SpecGetter, SpecSetter)]
pub struct MonitorHandle<'a> {
    handle: GhcbHyperPageHandle,
    guest_channel: SnpGuestChannel,
    gvca_page: Option<VBox<OnePage>>,
    vmsa: VBox<VmsaPage>,
    secret: &'a SnpSecretsPageLayout,
    stat: u64,
}

impl<'a> MonitorHandle<'a> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.handle.wf()
        &&& self.guest_channel.wf()
        &&& self.gvca_page.wf()
        &&& self.vmsa.is_vmsa_page()
        &&& self.secret.wf_mastersecret()
        &&& self.gvca_page.is_Some() ==> self.wf_registered()
    }

    pub closed spec fn wf_registered(&self) -> bool {
        let snp = self.gvca_page.get_Some_0().snp();
        &&& self.handle.wf()
        &&& self.guest_channel.wf()
        &&& self.gvca_page.is_Some()
        &&& self.gvca_page.get_Some_0().is_page()
        &&& !snp.is_confidential_to(1)
        &&& snp.is_confidential_to(2)
        &&& snp.is_confidential_to(3)
        &&& snp.is_confidential_to(4)
        &&& snp.pte().spec_encrypted()
        //&&& snp.rmp@[VMPL::from_int(RICHOS_VMPL as int)].is_super_of(OSMemPermSpec::readwrite().to_value().to_page_perm())
        &&& self.vmsa.is_vmsa_page()
        &&& self.secret.wf_mastersecret()
    }
}

pub fn run_richos(
    handle: GhcbHyperPageHandle, guest_channel: SnpGuestChannel,
    vmsa: VBox<VmsaPage>, secret: &SnpSecretsPageLayout,
    Tracked(nextvmpl_id): Tracked<CoreIdPerm>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>
)
requires
    0 < nextvmpl_id@.vmpl < 4,
    nextvmpl_id@.vmpl === vmsa@.vmpl.vspec_cast_to(),
    handle.wf(),
    guest_channel.wf(),
    old(cs).inv_stage_monitor(),
    vmsa.is_default_page(),
    vmsa@.is_constant(),
    secret.wf_mastersecret(),
ensures
    false,
{
    proof {reveal_strlit("Run richos.");}
    new_strlit("Run richos.").leak_debug();
    let vmpl: u8 = vmsa.borrow().vmpl.into();
    let (handle, vmsa) = handle.register_vmsa(vmpl, vmsa, Tracked(nextvmpl_id), Tracked(cs));
    let mut gvca_page = None;
    let mut mh = MonitorHandle{handle, guest_channel, vmsa, gvca_page, secret, stat: 0};
    assert(cs.inv_stage_monitor());
    loop
    invariant
        mh.wf(),
        cs.inv_stage_monitor(),
        vmsa.is_vmsa_page(),
    {
        let GhcbHyperPageHandle(ghcb, hypercall) = mh.handle;
        let (ghcb, vmsa) = ghcb.switch_to_next_vmpl(mh.vmsa, Tracked(&mut cs.snpcore));
        mh.handle = GhcbHyperPageHandle(ghcb, hypercall);
        mh.vmsa = vmsa;
        mh = mh.handle_richos(Tracked(cs));
    }
}
}

verus! {
#[derive(VPrint, IsConstant)]
pub struct GvcaHeader {
    pub gpa: u64,
    pub op: u32,
    pub cpu: u32,
    pub other: u64,
}
}

verus! {
impl GvcaHeader {
    pub fn from(rbx: u64, rcx: u64, rdx: u64) -> (ret: GvcaHeader)
    ensures
        ret.gpa === rbx,
        ret.op as int == rcx as u32 as int,
        ret.cpu as int == (rcx >> 32u64) as u32,
        ret.other == rdx,
    {
        GvcaHeader {
            gpa: rbx,
            op: rcx as u32,
            cpu: (rcx >> 32u64) as u32,
            other: rdx,
        }
    }

    pub fn gpn(&self) -> (ret: usize)
    requires
        self.gpa.spec_valid_addr_with(0),
    ensures
        ret == (self.gpa as int).to_page()
    {
        self.gpa.to_page() as usize
    }

    pub closed spec fn spec_has_gvca(&self) -> bool {
        self.gpa.spec_valid_addr_with(PAGE_SIZE as nat)
    }

    pub fn has_gvca(&self) -> (ret: bool)
    ensures
        ret == self.spec_has_gvca(),
    {
        self.gpa.check_valid_addr(PAGE_SIZE as u64)
    }

    pub fn npages(&self) -> (ret: u16)
    ensures
        ret as int == (self.gpa as int) % PAGE_SIZE!()
    {
        (self.gpa as usize % PAGE_SIZE) as u16
    }

    pub fn cpu(&self) -> (ret: u32)
    ensures
        ret == self.cpu
    {
        self.cpu
    }
}
}

verus! {
#[is_variant]
#[derive(SpecIntEnum)]
pub enum VmplReqOp {
    WakupAp = 0xffff_fffe,
    SetPrivate = 0x1,
    SetShared = 0x2,
    Register = 0x3,
    ExtendPcr = 0x4,
    LockKernExe = 0x5,
    Attest = 0x6,
    Secret = 0x7,
    Encrypt = 0x8,
    Decrypt = 0x9,
}
}

verismo_simple! {
#[repr(C, align(1))]
pub struct EncryptReq {
    pub index: u32,
    pub data: Array<u8, 4092>,
}
}

verismo_simple! {
    #[repr(C, align(1))]
    #[derive(VClone, Copy)]
    pub struct LockKernEntry {
        pub start: u64,
        pub end: u64,
    }

    pub type LockKernReq = [LockKernEntry; {PAGE_SIZE/16}];
}

verus! {
impl<'a> MonitorHandle<'a> {
    pub fn parse_and_handle_vmpl_req(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Self)
    requires
        self.wf(),
        old(cs).inv_stage_monitor(),
    ensures
        ret.wf(),
        cs.inv_stage_monitor(),
    {
        let mut mhandle = self;
        let GhcbHyperPageHandle(ghcb, hypercall) = mhandle.handle;
        let vmsa = mhandle.vmsa;
        assert(vmsa.is_vmsa_page());
        let (vmsapage_ptr, Tracked(vmsa_perm)) = vmsa.into_raw();
        let vmsa_ptr = vmsapage_ptr;
        assert(vmsa_perm@.wf());
        let (mut rax, Tracked(vmsa_perm)) = vmsa_ptr.rax().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        assert(vmsa_perm@.wf());
        let mut magic_check = rax.sec_eq(&SNP_VMPL_REQ_MAGIC.into());
        magic_check.declassify();
        let magic_check = magic_check.reveal_value();
        if !magic_check {
            vc_terminate(SM_TERM_UNSUPPORTED, Tracked(&mut cs.snpcore));
        }
        let (mut rbx, Tracked(vmsa_perm)) = vmsa_ptr.rbx().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        let (mut rcx, Tracked(vmsa_perm)) = vmsa_ptr.rcx().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        let (mut rdx, Tracked(vmsa_perm)) = vmsa_ptr.rdx().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        rbx.declassify();
        rcx.declassify();
        rdx.declassify();
        let req = GvcaHeader::from(rbx.into(), rcx.into(), rdx.into());

        // Restore ghcb MSR value due to a hyperv bug;
        let ghcb_addr = ghcb.get_const_addr();
        let tracked mut ghcb_msr_perm = cs.snpcore.regs.tracked_remove(GHCB_REGID());
        MSR_GHCB().write(ghcb_addr.into(), Tracked(&mut ghcb_msr_perm));
        proof{
            cs.snpcore.regs.tracked_insert(GHCB_REGID(), ghcb_msr_perm);
        }

        // Check VMPL privilege.
        let (vmpl, Tracked(vmsa_perm))  = vmsa_ptr.vmpl().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        let mut check_vmpl = vmpl.sec_eq(&u8_s::constant(RICHOS_VMPL));
        check_vmpl.declassify();
        if !check_vmpl.reveal_value()  {
            vc_terminate(SM_TERM_RICHOS_ERR(0), Tracked(&mut cs.snpcore))
        };

        mhandle.vmsa = VBox::from_raw(vmsa_ptr.to_usize(), Tracked(vmsa_perm));
        mhandle.handle = GhcbHyperPageHandle(ghcb, hypercall);
        let ret = mhandle.handle_vmpl_request(&req, RICHOS_VMPL, Tracked(cs));
        match ret {
            Err(code) => {
                vc_terminate(SM_TERM_RICHOS_ERR(code as u64), Tracked(&mut cs.snpcore))
            }
            Ok(mh) => {
                mhandle = mh;
            }
        }
        mhandle
    }

    fn handle_mk_private_shared(
        self,
        vmpl: u8,
        gpn: usize,
        npages: u16,
        is_priv: bool,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>
    ) -> (ret: Result<Self, u8>)
    requires
        self.wf(),
        old(cs).inv_stage_monitor(),
    ensures
        ret.is_Ok() ==> ret.get_Ok_0().wf(),
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid(), spec_PT_lockid()]),
    {
        if npages == 0 {
            return Ok(self);
        }

        if !gpn.check_valid_pn(npages as usize) {
            new_strlit("Invalid GPN npages pair\n").leak_debug();
            return Err(SM_TERM_RICHOS_ERR(0) as u8);
        }

        let ghost cs1 = *cs;
        let ret = self._handle_mk_private_shared(vmpl, gpn, npages, is_priv, Tracked(cs));
        let ghost cs2 = *cs;
        match ret {
            Ok((mhandle, real_npages)) => {
                if real_npages < npages as usize{
                    let ret = mhandle.handle_mk_private_shared(
                        vmpl, gpn + real_npages, npages - real_npages as u16, is_priv, Tracked(cs)
                    );
                    proof {
                        cs1.lemma_update_prop(cs2, *cs, set![], set![spec_OSMEM_lockid(), spec_PT_lockid()], set![], set![spec_OSMEM_lockid(), spec_PT_lockid()]);
                    }
                    ret
                } else {
                    Ok(mhandle)
                }
            }
            Err(e) => {
                Err(e)
            }
        }
    }

    fn _handle_mk_private_shared(
        self,
        _vmpl: u8,
        gpn: usize,
        npages: u16,
        is_priv: bool,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>
    ) -> (ret: Result<(Self, usize), u8>)
    requires
        self.wf(),
        old(cs).inv_stage_monitor(),
        npages > 0,
    ensures
        ret.is_Ok() ==> ret.get_Ok_0().0.wf(),
        ret.is_Ok() ==> ret.get_Ok_0().1 <= npages,
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid(), spec_PT_lockid()]),
    {
        let ghost cs1 = *cs;
        let tracked osmem_lock = cs.lockperms.tracked_remove(spec_OSMEM_lockid());
        let (osmem_ptr,  Tracked(mut osmem_perm), Tracked(mut osmem_lock))= OSMEM().acquire(Tracked(osmem_lock), Tracked(&cs.snpcore.coreid));
        let mut osmem = osmem_ptr.take(Tracked(&mut osmem_perm));
        let mut entry;
        let mut i;
        if let Some(e) = osmem_check_and_get(&mut osmem, gpn, OSMemPerm::ram()) {
            entry = e.1;
            i = e.0;
        } else {
            osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
            OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
            proof {
                cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
            }
            (new_strlit("Invalid perm from richos\n"), gpn).leak_debug();
            return Result::Err(SM_TERM_RICHOS_ERR(0) as u8);
        }

        let entry_start: usize = entry.start_page.into();
        let entry_end: usize = entry.end();
        let expected_gpn_end = gpn + npages as usize;
        let npages = if entry_end > expected_gpn_end { npages as usize } else {entry_end - gpn};

        let (left, entry, right) = osmem_entry_split(entry, gpn, npages);

        let mut mhandle = self;
        let GhcbHyperPageHandle(mut ghcb_h, hyperpage_h) = mhandle.handle;

        let ghost cs2 = *cs;
        let (ghcb_h, entry) = osmem_adjust(ghcb_h, entry, !is_priv, Tracked(cs));

        let entry  = osmem_entry_merge(left, entry);
        let entry  = osmem_entry_merge(entry, right);
        osmem.insert(i, entry);

        proof{assert(osmem_wf(osmem@));}

        osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
        OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
        let ghost cs3 = *cs;
        proof {
            cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
        }
        proof{
            LockMap::lemma_lock_update_auto();
            SnpCore::lemma_regs_update_auto();
            assert(cs.snpcore.only_reg_coremode_updated(cs1.snpcore, set![]));
            assert(cs.lockperms[spec_OSMEM_lockid()]@.points_to.only_val_updated(cs1.lockperms[spec_OSMEM_lockid()]@.points_to));
            assert(cs.lockperms[spec_PT_lockid()]@.points_to.only_val_updated(cs1.lockperms[spec_PT_lockid()]@.points_to));
            assert(cs.lockperms.updated_lock(&cs1.lockperms, set![spec_OSMEM_lockid(), spec_PT_lockid()])) by {
                assert forall |id: int|
                !(set![spec_OSMEM_lockid(), spec_PT_lockid()].contains(id)) && cs1.lockperms.contains_key(id)
                implies (#[trigger]cs.lockperms[id]) === cs1.lockperms[id] && cs.lockperms.contains_key(id)
                by{
                    assert(id != spec_OSMEM_lockid());
                    assert(id != spec_PT_lockid());
                    assert(cs1.lockperms.contains_key(id));
                    assert(cs2.lockperms.contains_key(id));
                    assert(cs3.lockperms.contains_key(id));
                    assert(cs.lockperms.contains_key(id));
                }
            }
        }

        mhandle.handle = GhcbHyperPageHandle(ghcb_h, hyperpage_h);
        //new_strlit("End of handle_mk_private_shared\n").leak_debug();
        Result::Ok((mhandle, npages))
    }

    fn handle_wakeup_ap(&self, vmsa_gpn: usize, cpu: usize, vmpl: u8,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>)
        -> (ret: Result<(), u8>)
    requires
        vmsa_gpn.spec_valid_pn_with(1),
        1 <= vmpl < 4,
        old(cs).inv_stage_monitor(),
        cpu < 0x10000_0000,
        self.wf(),
    ensures
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid(), spec_PT_lockid(), spec_RICHOS_VMSA_lockid()]),
    {
        let vmsa_gpa = vmsa_gpn.to_addr();
        if !vmsa_gpa.check_valid_addr(PAGE_SIZE) {
            return Err(SM_TERM_RICHOS_ERR(3) as u8);
        }
        let ghost used_locks = set![spec_OSMEM_lockid(), spec_PT_lockid(), spec_RICHOS_VMSA_lockid()];
        assert(used_locks =~~= set![spec_OSMEM_lockid(), spec_PT_lockid()].union(set![spec_RICHOS_VMSA_lockid()]));
        assert(set![spec_OSMEM_lockid(), spec_PT_lockid()] =~~= set![spec_OSMEM_lockid()].union(set![spec_PT_lockid()]));
        assert(cs.lockperms.contains_key(spec_OSMEM_lockid()));
        let ghost cs1 = *cs;
        let tracked osmem_lock = cs.lockperms.tracked_remove(spec_OSMEM_lockid());
        let (osmem_ptr, Tracked(mut osmem_perm), Tracked(mut osmem_lock))= OSMEM().acquire(Tracked(osmem_lock), Tracked(&cs.snpcore.coreid));
        let mut osmem = osmem_ptr.take(Tracked(&mut osmem_perm));
        let ret = if let Some((vmsa, osperm)) = osmem_check_and_get_page(&mut osmem, vmsa_gpn, OSMemPerm::ram(), Tracked(cs)) {
            Ok(vmsa)
        } else {
            Err(SM_TERM_RICHOS_ERR(4) as u8)
        };
        osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
        OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
        proof{
            cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
            assert(cs.only_lock_reg_coremode_updated(cs1, set![], set![spec_OSMEM_lockid(), spec_PT_lockid()]));
        }

        let ghost cs2 = *cs;
        match ret {
            Err(e) => {
                return Err(e);
            }
            _ => {}
        }
        let vmsa = ret.unwrap();
        let tracked mut vmsa_lock = cs.lockperms.tracked_remove(spec_RICHOS_VMSA_lockid());
        let (vmsa_vec_ptr,  Tracked(mut vmsa_vec_perm), Tracked(mut vmsa_lock))= RICHOS_VMSA().acquire(Tracked(vmsa_lock), Tracked(&cs.snpcore.coreid));
        let mut vmsa_vec = vmsa_vec_ptr.take(Tracked(&mut vmsa_vec_perm));
        let ghost prev_vmsa_vec = vmsa_vec;
        fill_vec(&mut vmsa_vec, cpu + 1);
        vmsa_vec.set(cpu, Some(vmsa));
        proof{
            assert(richos_vmsa_invfn()(vmsa_vec)) by {
                assert forall |i| 0 <= i < vmsa_vec.len()
                implies
                    vmsa_vec[i].is_Some() ==> (#[trigger]vmsa_vec[i]).get_Some_0().is_page()
                by {
                    if vmsa_vec[i].is_Some() {
                        assert(i == cpu || prev_vmsa_vec[i] === vmsa_vec[i]);
                    }
                }
            }
        }
        vmsa_vec_ptr.put(Tracked(&mut vmsa_vec_perm), vmsa_vec);
        RICHOS_VMSA().release(Tracked(&mut vmsa_lock), Tracked(vmsa_vec_perm), Tracked(&cs.snpcore.coreid));

        proof {
            cs.lockperms.tracked_insert(spec_RICHOS_VMSA_lockid(), vmsa_lock);
            cs1.lemma_update_prop(cs2, *cs, set![], set![spec_OSMEM_lockid(), spec_PT_lockid()], set![], set![spec_RICHOS_VMSA_lockid()]);
        }
        Ok(())
    }

    pub fn handle_register(&mut self, gpn: usize,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>
    ) -> (ret: bool)
    requires
        old(cs).inv_stage_monitor(),
        old(self).wf(),
    ensures
        self.wf(),
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid(), spec_PT_lockid()]),
        *self === (*old(self)).spec_set_gvca_page(self.spec_gvca_page()),
        ret ==> self.wf_registered(),
    {
        let tracked osmem_lock = cs.lockperms.tracked_remove(spec_OSMEM_lockid());
        let (osmem_ptr, Tracked(mut osmem_perm), Tracked(mut osmem_lock))= OSMEM().acquire(Tracked(osmem_lock), Tracked(&cs.snpcore.coreid));
        let mut osmem = osmem_ptr.take(Tracked(&mut osmem_perm));
        let ret = if let Some((gvca, osperm)) = osmem_check_and_get_page(&mut osmem, gpn, OSMemPerm::empty().set_read(1).set_write(1), Tracked(cs)) {
            self.gvca_page = Some(gvca);
            assume(self.wf_registered());
            true
        } else {
            new_strlit("failed to register GVCA\n").leak_debug();
            false
        };
        osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
        OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
        proof{
            cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
        }
        ret
    }

    fn handle_extend_pcr(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Self)
    requires
        old(cs).inv_stage_monitor(),
        old(cs).inv_stage_pcr(),
        self.wf(),
    ensures
        ret.wf(),
        cs.inv_stage_monitor(),
        cs.inv_stage_pcr(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_PCR_lockid()]),
    {
        use crate::security::pcr::*;
        let mut mhandle = self;
        if let Some(gvca) = mhandle.gvca_page {
            let req: VBox<ExtendPCRReq> = gvca.to();
            let val = req.copy_val();
            extend_pcr(0, &val, Tracked(cs));
            proof{
                assert(req.snp() === gvca.snp());
                assert(req.id() === gvca.id());
            }
            mhandle.gvca_page = Some(req.to());
        } else {
            new_strlit("Please register gvca page!!\n").leak_debug();
        }
        mhandle
    }

    fn handle_attest(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Self)
    requires
        self.gvca_page.is_Some(),
        old(cs).inv_stage_monitor(),
        old(cs).inv_stage_pcr(),
        self.wf(),
    ensures
        ret.wf(),
        cs.inv_stage_monitor(),
        cs.inv_stage_pcr(),
        ret.wf(),
    {
        use crate::security::pcr::attest_pcr;
        let mut mhandle = self;

        if let Some(gvca) = mhandle.gvca_page {
            let GhcbHyperPageHandle(ghcb_h, hyperpage_h) = mhandle.handle;
            let report = VBox::new_uninit(Tracked(cs));
            let (report, guest_channel, ghcb_h) = attest_pcr(
                mhandle.guest_channel, ghcb_h, mhandle.secret, 0, report, Tracked(cs));
            mhandle.handle = GhcbHyperPageHandle(ghcb_h, hyperpage_h);
            mhandle.guest_channel = guest_channel;
            assert(gvca.wf());

            // TODO: information flow declassification.
            assume(report@.is_constant_to(RICHOS_VMPL as nat));
            let mut gvca_report  = gvca.to();
            mhandle.gvca_page = Some(gvca_report.set(report).to());
        } else {
            new_strlit("Please register gvca page!!\n").leak_debug();
        }
        mhandle
    }

    fn handle_lock_kernel(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Self)
    requires
        old(cs).inv_stage_monitor(),
        self.wf(),
        self.gvca_page.is_Some(),
    ensures
        ret.wf(),
        ret.gvca_page.is_Some(),
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid()]),
    {
        use crate::security::pcr::*;
        let mut mhandle = self;
        assert(spec_size::<LockKernReq>() == PAGE_SIZE) by {
            assert(spec_size::<LockKernEntry>() == 16);
            assert(spec_size::<LockKernEntry>() * (PAGE_SIZE / 16) == PAGE_SIZE);
        }
        let req: VBox<LockKernReq> = mhandle.gvca_page.unwrap().to();
        let (gvca_ptr, Tracked(mut perm)) = req.into_raw();
        let priv_req = gvca_ptr.take(Tracked(&mut perm));
        let mut entries = create_lock_entries(&priv_req);

        let tracked osmem_lock = cs.lockperms.tracked_remove(spec_OSMEM_lockid());
        let (osmem_ptr, Tracked(mut osmem_perm), Tracked(mut osmem_lock)) = OSMEM().acquire(Tracked(osmem_lock), Tracked(&cs.snpcore.coreid));
        let mut osmem = osmem_ptr.take(Tracked(&mut osmem_perm));
        lock_kernel(&mut osmem, &entries, Tracked(&mut cs.snpcore));
        osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
        OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
        proof {
            cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
        }
        gvca_ptr.put(Tracked(&mut perm), priv_req);
        mhandle.gvca_page = Some(VBox::from_raw(gvca_ptr.to_usize(), Tracked(perm.tracked_into_raw().tracked_into())));
        mhandle
    }

    #[verifier(external_body)]
    fn handle_vmpl_request(
        self, req: &GvcaHeader, vmpl: u8, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Result<Self, u8>)
    requires
        old(cs).inv_stage_monitor(),
        1 <= vmpl < 4,
        self.wf(),
    ensures
        ret.is_Ok() ==> ret.get_Ok_0().wf(),
        cs.inv_stage_monitor(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid()])
    {
        let op = VmplReqOp::from_u64(req.op as u64);
        match op {
            Option::Some(op) => match op {
                VmplReqOp::WakupAp if req.has_gvca() => {
                    let vmsa_gpn = req.gpn();
                    let cpu = req.cpu();
                    let ret = self.handle_wakeup_ap(vmsa_gpn, cpu as usize, vmpl, Tracked(cs));
                    match ret{
                        Ok(_) => {
                            Ok(self)
                        }
                        Err(e) => {
                            Err(e)
                        }
                    }
                }
                VmplReqOp::SetPrivate => {
                    self.handle_mk_private_shared(vmpl, req.gpn(), req.npages(), true, Tracked(cs))
                }
                VmplReqOp::SetShared => {
                    self.handle_mk_private_shared(vmpl, req.gpn(), req.npages(), false, Tracked(cs))
                }
                VmplReqOp::Register => {
                    new_strlit("Register").leak_debug();
                    let mut h = self;
                    if h.handle_register(req.gpn(), Tracked(cs)) {
                        Ok(h)
                    } else {
                        Err(SM_TERM_RICHOS_ERR(4) as u8)
                    }
                }
                VmplReqOp::Attest if req.has_gvca() => {
                    new_strlit("Attest").leak_debug();
                    Ok(self.handle_attest(Tracked(cs)))
                }
                VmplReqOp::ExtendPcr if req.has_gvca() => {
                    new_strlit("ExtendPcr").leak_debug();
                    Ok(self.handle_extend_pcr(Tracked(cs)))
                }
                VmplReqOp::LockKernExe if req.has_gvca() && self.gvca_page.is_some() => {
                    Ok(self.handle_lock_kernel(Tracked(cs)))
                }
                VmplReqOp::Secret if req.has_gvca() => {
                    new_strlit("Secret").leak_debug();
                    Ok(self)
                    //handle_secret_gen(&gvca, state)
                }
                VmplReqOp::Encrypt if req.has_gvca() => {
                    new_strlit("Encrypt").leak_debug();
                    Ok(self)
                    //handle_encrypt(&gvca, true, state)
                }
                VmplReqOp::Decrypt if req.has_gvca() => {
                    new_strlit("Decrypt").leak_debug();
                    Ok(self)
                    //handle_encrypt(&gvca, false, state)
                }
                _ => {
                    Ok(self)
                }
            },
            Option::None => {
                Err(SM_TERM_UNSUPPORTED as u8)
            }
        }

    }

    pub fn handle_richos(self, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: Self)
    requires
        self.wf(),
        old(cs).inv_stage_monitor(),
    ensures
        cs.inv_stage_monitor(),
        //cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_OSMEM_lockid()]),
        ret.wf(),
    {
        let mut mhandle = self;
        let (vmsa_ptr, Tracked(vmsa_perm)) = mhandle.vmsa.into_raw();
        let (mut exit_code, Tracked(vmsa_perm)) = vmsa_ptr.guest_error_code().copy_with::<VmsaPage>(Tracked(vmsa_perm));
        mhandle.vmsa = VBox::from_raw(vmsa_ptr.to_usize(), Tracked(vmsa_perm));
        proof {
            assert(exit_code.wf_value());
        }
        exit_code.declassify();
        match SVMExitCode::from_u64(exit_code.into()) {
            Option::Some(code) => match code {
                SVMExitCode::VmgExit => {
                    mhandle = mhandle.parse_and_handle_vmpl_req(Tracked(cs));
                }
                _ => {
                    vc_terminate(SM_TERM_UNSUPPORTED, Tracked(&mut cs.snpcore));
                }
            },
            Option::None => {
                vc_terminate(SM_TERM_UNSUPPORTED, Tracked(&mut cs.snpcore));
            }
        }
        // Clear error code
        mhandle.vmsa.set_guest_error_code(u64_s::new(0));
        mhandle
    }
}
}

verus! {
pub fn start_richos(
    mparam: &MonitorParams,
    secret: &SnpSecretsPageLayout,
    cpuid: VBox<SnpCpuidTable>,
    hvparam: VBox<OnePage>,
    guest_channel: SnpGuestChannel,
    handle: GhcbHyperPageHandle,
    Tracked(nextvmpl_id): Tracked<CoreIdPerm>,
    Tracked(richos_perm): Tracked<SnpPointsToRaw>,
    Tracked(acpi_perms): Tracked<Map<int, SnpPointsToRaw>>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>
)
requires
    old(cs).inv_stage_monitor(),
    mparam.mp_wf(),
    secret.wf_mastersecret(),
    cpuid.is_default_page(),
    hvparam.is_default_page(),
    hvparam@.is_constant(),
    cpuid@.is_constant(),
    handle.wf(),
    guest_channel.wf(),
    nextvmpl_id@.vmpl == RICHOS_VMPL,
    spec_is_default_pages_const_to_vmpl(acpi_perms,
        mparam.acpi.spec_to_page().vspec_cast_to(),
        mparam.acpi_size.spec_to_page().vspec_cast_to(), RICHOS_VMPL as nat),
    richos_perm@.wf_const_default(
        (mparam.richos_start.vspec_cast_to(),
        mparam.richos_size.vspec_cast_to())),
ensures
    false,
{
    proof {reveal_strlit("Start richos ");}
    (new_strlit("Start richos "), mparam.richos_size).leak_debug();

    if mparam.richos_size.reveal_value() == 0 {
        vc_terminate(SM_TERM_RICHOS_ERR(1), Tracked(&mut cs.snpcore));
    }

    let ghost cs1 = *cs;
    let tracked osmem_lock = cs.lockperms.tracked_remove(spec_OSMEM_lockid());
    let (osmem_ptr,  Tracked(mut osmem_perm), Tracked(mut osmem_lock))= OSMEM().acquire(Tracked(osmem_lock), Tracked(&cs.snpcore.coreid));
    let mut osmem = osmem_ptr.take(Tracked(&mut osmem_perm));
    let ghost cs2 = *cs;
    // Assign ACPI table to VMPL2
    let acpi_start_page = mparam.acpi.to_page().into();
    let acpi_pages = mparam.acpi_size.to_page().into();

    osmem_add(&mut osmem, acpi_start_page, acpi_pages, OSMemPerm::empty().set_write(1).set_read(1).set_kern_exe(1), false,
        Tracked(acpi_perms), Tracked(&mut cs.snpcore));
    let ghost cs3 = *cs;
    proof{
        assert(cs.inv_stage_common());
        assert(RICHOS_VMPL == 1);
    }
    new_strlit("GhcbHyperPageHandle\n").leak_debug();

    let GhcbHyperPageHandle(ghcb_h, hyperpage_h) = handle;
    new_strlit("richos_early_ghcb\n").leak_debug();
    let (richos_early_ghcb, ghcb_h) = VBox::<OnePage>::new_shared_page(0x2000000, ghcb_h, Tracked(cs));
    let handle = GhcbHyperPageHandle(ghcb_h, hyperpage_h);
    let ghost cs4 = *cs;
    let (vmsa, cpuid) = load_bzimage_to_vmsa(
        &mut osmem, mparam, RICHOS_VMPL, secret, cpuid, hvparam, richos_early_ghcb,
        Tracked(richos_perm), Tracked(cs)
    );
    let ghost cs5 = *cs;
    proof{
        cs2.lemma_update_prop(cs3, cs4, set![], set![], set![], set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
        cs2.lemma_update_prop(cs4, cs5, set![], set![spec_ALLOCATOR_lockid(), spec_PT_lockid()], set![], set![spec_ALLOCATOR_lockid()]);
    }
    osmem_ptr.put(Tracked(&mut osmem_perm), osmem);
    OSMEM().release(Tracked(&mut osmem_lock), Tracked(osmem_perm), Tracked(&cs.snpcore.coreid));
    proof {
        cs.lockperms.tracked_insert(spec_OSMEM_lockid(), osmem_lock);
        assert(cs.only_lock_reg_coremode_updated(cs1, set![], set![spec_OSMEM_lockid(), spec_PT_lockid(), spec_ALLOCATOR_lockid()]));
    }
    let ghost cs6 = *cs;
    // enable VTL protection
    //
    let handle = handle.config_partition(Tracked(cs));

    run_richos(handle, guest_channel, vmsa, secret, Tracked(nextvmpl_id), Tracked(cs));
}
}

use super::*;
use crate::mshyper::GhcbHyperPageHandle;
use crate::trusted_hacl::SHA512Type;

verismo_simple! {
#[repr(C, align(1))]
#[derive(SpecGetter, SpecSetter, Copy, VClone)]
pub struct SnpSecretsPageLayout {
    version: u32,
    imien: u32,
    fms: u32,
    reserved_2: u32,
    gosvw: Array<u8, 16>,
    vmpck0: AESKey256,
    vmpck1: AESKey256,
    vmpck2: AESKey256,
    vmpck3: AESKey256,
    os_area: SecretsOSArea,
    reserved_3: Array<u8, 3840>,
}
}

verismo_simple! {
    #[repr(C, align(1))]
    #[derive(SpecGetter, SpecSetter, VClone, Copy)]
    pub struct SnpGuestMsgHdr {
        #[def_offset]
        authtag: AESAuthTag,
        msg_seqno: u64,
        reserved1: u64,
        #[def_offset]
        algo: u8,
        hdr_version: u8,
        hdr_sz: u16,
        msg_type: u8,
        msg_version: u8,
        msg_sz: u16,
        reserved2: u32,
        msg_vmpck: u8,
        reserved3: Array<u8, 35>,
    }
}

verus! {

impl SnpSecretsPageLayout {
    pub closed spec fn closed_wf_mastersecret(&self) -> bool {
        &&& self.vmpck0@.is_fullsecret()
        &&& self.vmpck1@.is_constant_to(1)
        &&& self.vmpck1@.is_fullsecret_to(2)
        &&& self.vmpck1@.is_fullsecret_to(3)
        &&& self.vmpck1@.is_fullsecret_to(4)
        &&& self.vmpck2@.is_constant_to(2)
        &&& self.vmpck2@.is_fullsecret_to(1)
        &&& self.vmpck2@.is_fullsecret_to(3)
        &&& self.vmpck2@.is_fullsecret_to(4)
        &&& self.vmpck3@.is_constant_to(3)
        &&& self.vmpck3@.is_fullsecret_to(1)
        &&& self.vmpck3@.is_fullsecret_to(2)
        &&& self.vmpck3@.is_fullsecret_to(4)
        &&& self.os_area.is_constant()
    }

    pub open spec fn wf_mastersecret(&self) -> bool {
        &&& self.wf()
        &&& self.closed_wf_mastersecret()
    }
}

} // verus!
verismo_simple! {
impl SnpGuestChannel {
    pub fn new(handle: GhcbHandle, Tracked(cs): Tracked<&mut SnpCoreSharedMem>) -> (ret: (SnpGuestChannel, GhcbHandle))
    requires
        handle.ghcb_wf(),
        old(cs).inv(),
    ensures
        cs.inv(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]),
        ret.0.wf(),
        ret.1.ghcb_wf(),
    {
        let ghost oldcs = *cs;
        let (req, handle) = handle.new_shared_vpage(Tracked(cs));
        let ghost prevcs = *cs;
        let (resp, handle) = handle.new_shared_vpage(Tracked(cs));
        /*
        let (report_req, handle) = VBox::new_aligned(
            8, SnpReportReq{user_data: Array::new(0), vmpl: 0, reserved: Array::new(0)}
            Tracked(cs));*/
        proof{
            oldcs.lemma_update_prop(prevcs, *cs, set![], set![spec_ALLOCATOR_lockid(), spec_PT_lockid()], set![], set![spec_ALLOCATOR_lockid(), spec_PT_lockid()]);
        }
        (SnpGuestChannel {req, resp}, handle)
    }
}

}

verus! {

pub struct FillSecretForVMPL<'a> {
    pub master_secret: &'a SnpSecretsPageLayout,
    pub vmpl: u8,
}

pub struct FillSecretForVMPLOut;

impl<'a, 'b> MutFnTrait<'a, FillSecretForVMPL<'b>, FillSecretForVMPLOut> for SnpSecretsPageLayout {
    open spec fn spec_update_requires(&self, params: FillSecretForVMPL<'b>) -> bool {
        let FillSecretForVMPL { master_secret, vmpl } = params;
        &&& master_secret.wf_mastersecret()
        &&& self.is_constant()
        &&& 0 < vmpl < 4
    }

    open spec fn spec_update(
        &self,
        prev: &Self,
        params: FillSecretForVMPL<'b>,
        ret: FillSecretForVMPLOut,
    ) -> bool {
        let FillSecretForVMPL { master_secret, vmpl } = params;
        &&& if vmpl == 1 {
            self.spec_vmpck1() === master_secret.spec_vmpck1()
        } else if vmpl == 2 {
            self.spec_vmpck2() === master_secret.spec_vmpck2()
        } else if vmpl == 3 {
            self.spec_vmpck3() === master_secret.spec_vmpck3()
        } else {
            true
        }
        &&& self.is_constant_to(vmpl as nat)
    }

    fn box_update(&'a mut self, params: FillSecretForVMPL<'b>) -> (ret: FillSecretForVMPLOut) {
        let FillSecretForVMPL { master_secret, vmpl } = params;
        assert(self.is_constant());
        assert(self.is_constant_to(vmpl as nat));  // proof required
        if vmpl == 1 {
            self.vmpck1 = master_secret.vmpck1.clone();
        } else if vmpl == 2 {
            self.vmpck2 = master_secret.vmpck2.clone();
        } else if vmpl == 3 {
            self.vmpck3 = master_secret.vmpck3.clone();
        }
        FillSecretForVMPLOut
    }
}

} // verus!
verus! {

proof fn proof_msg_hdr_size()
    ensures
        spec_size::<SnpGuestMsgHdr>() == 0x60,
{
}

} // verus!
verismo_simple! {
pub fn enc_dec(
    enc: bool,
    key: &AESKey256,
    iv: &AESInv,
    ad: &AESAddInfo,
    tag: &AESAuthTag,
    len: u32,
    plain_addr: usize_t,
    cipher_addr: usize_t,
    Tracked(plain_perm): Tracked<SnpPointsToRaw>,
    Tracked(cipher_perm): Tracked<SnpPointsToRaw>,
) -> (perms: (Tracked<SnpPointsToRaw>, Tracked<SnpPointsToRaw>))
requires
    plain_perm@.wf_default((plain_addr as int, len as nat)),
    cipher_perm@.wf_default((cipher_addr as int, len as nat)),
    key@.is_fullsecret(),
ensures
    enc ==> perms.0@ === plain_perm,
    enc ==> perms.1@@.wf_const_default((cipher_addr as int, len as nat)),
    enc ==> perms.1@@.only_val_updated(cipher_perm@),
    !enc ==> perms.1@ === cipher_perm,
    !enc ==> perms.0@@.wf_default((plain_addr as int, len as nat)),
    !enc ==> perms.0@@.only_val_updated(plain_perm@),
{
    let tracked mut cipher_perm = cipher_perm;
    let tracked mut plain_perm = plain_perm;
    if enc {
        raw_encrypt(key, iv, ad, tag, len, plain_addr, cipher_addr,
            Tracked(&plain_perm), Tracked(&mut cipher_perm));
        assert(cipher_perm@.bytes().is_constant());
        assert(cipher_perm@.wf_const_default((cipher_addr as int, len as nat)));
    } else {
        raw_decrypt(key, iv, ad, tag, len, plain_addr, cipher_addr,
            Tracked(&mut plain_perm), Tracked(&cipher_perm));
        assert(plain_perm@.bytes().wf());
        assert(plain_perm@.wf_default((plain_addr as int, len as nat)));
    }
    (Tracked(plain_perm), Tracked(cipher_perm))
}
}

verismo_simple! {
pub fn enc_dec_payload(
    enc: bool,
    key: &AESKey256,
    msg: VBox<SnpGuestMsg>,
    msg_no: u64_s,
    plain_addr: usize_t,
    Tracked(plain_perm): Tracked<SnpPointsToRaw>,
) -> (ret: (VBox<SnpGuestMsg>, Tracked<SnpPointsToRaw>))
requires
    msg_no.wf(),
    msg.wf(),
    msg@.is_constant_to(RICHOS_VMPL as nat),
    msg@.snphdr.is_constant(),
    msg.snp().is_default(),
    key@.is_fullsecret(),
    msg@.snphdr.spec_msg_sz() <= MAX_SNP_MSG_SZ,
    plain_perm@.wf_default((plain_addr as int, msg@.snphdr.spec_msg_sz() as nat)),
ensures
    ret.0.wf(),
    ret.0.only_val_updated(msg),
    !enc ==> ret.0@ === msg@,
    ret.1@@.wf_default((plain_addr as int, msg@.snphdr.spec_msg_sz() as nat)),
    !enc ==> ret.1@@.only_val_updated(plain_perm@),
    enc ==> ret.1@ === plain_perm,
    ret.0@.snphdr.is_constant(),
    enc ==> ret.0@.is_constant_to(RICHOS_VMPL as nat),
{
    let mut iv: AESInv = Array::new(0u8_s);
    iv.set(0usize_t, (msg_no as u8));
    iv.set(1usize_t, ((msg_no >> 8) as u8));
    iv.set(2usize_t, ((msg_no >> 16) as u8));
    iv.set(3usize_t, ((msg_no >> 24) as u8));
    let mut msg_len = msg.borrow().snphdr.msg_sz as u32;

    proof{
        proof_into_is_constant::<_, SecSeqByte>(msg@);
    }
    let (msg_ptr, Tracked(mut msg_perm)) = msg.into_raw();

    let tracked mut msg_perm = msg_perm.tracked_into_raw();
    let ghost old_msg_perm = msg_perm;
    let tracked (mut msg_hdr_perm, mut payload_perm) = msg_perm.tracked_split(spec_size::<SnpGuestMsgHdr>());
    let tracked (mut left, mut ad_perm_right) = msg_hdr_perm.tracked_split(SnpGuestMsgHdr::spec_algo_offset());
    let tracked (ad_perm, right) = ad_perm_right.tracked_split(spec_size::<AESAddInfo>());

    let tracked (tag_perm, mid) = left.tracked_split(spec_size::<AESAuthTag>());

    let tracked (cipher_perm, payload_right) = payload_perm.tracked_split(msg_len as nat);
    proof{
        assert(old_msg_perm@.bytes() =~~= tag_perm@.bytes() + mid@.bytes() + ad_perm@.bytes() + right@.bytes() + cipher_perm@.bytes() + payload_right@.bytes());
        assert(old_msg_perm@.bytes().is_constant_to(RICHOS_VMPL as nat));
    }
    let tag: VBox<AESAuthTag> = VBox::from_raw(
        msg_ptr.snphdr().authtag().to_usize(), Tracked(tag_perm.tracked_into()));
    let ad: VBox<AESAddInfo> = VBox::from_raw(
        msg_ptr.snphdr().algo().to_usize(), Tracked(ad_perm.tracked_into()));
    let cipher_addr: usize_t = msg_ptr.payload().to_usize();

    let (Tracked(plain_perm), Tracked(cipher_perm)) = enc_dec(
        enc, key, &iv, ad.borrow(), tag.borrow(), msg_len,
        plain_addr, cipher_addr,
        Tracked(plain_perm),
        Tracked(cipher_perm),
    );
    proof{cipher_perm@.bytes().is_constant_to(RICHOS_VMPL as nat);}
    let (_, Tracked(tag_perm)) = tag.into_raw();
    let (_, Tracked(ad_perm)) = ad.into_raw();
    proof{
        let tracked tag_perm = tag_perm.tracked_into_raw();
        let tracked ad_perm = ad_perm.tracked_into_raw();
        msg_perm =  tag_perm.tracked_join(mid)
                            .tracked_join(ad_perm)
                            .tracked_join(right)
                            .tracked_join(cipher_perm)
                            .tracked_join(payload_right);
        assert(msg_perm@.bytes() =~~= tag_perm@.bytes() + mid@.bytes() + ad_perm@.bytes() + right@.bytes() + cipher_perm@.bytes() + payload_right@.bytes());
        assert(msg_perm@.bytes().is_constant());
        proof_into_is_constant::<_, SnpGuestMsg>(msg_perm@.bytes());
    }
    (VBox::from_raw(msg_ptr.to_usize(), Tracked(msg_perm.tracked_into())), Tracked(plain_perm))
}
}

verus! {

pub fn enc_payload(
    secret: &SnpSecretsPageLayout,
    version: u8,
    msg_no: u64,
    msg_type: u8,
    payload_addr: usize,
    len: u16,
    Tracked(payload_perm): Tracked<SnpPointsToRaw>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: (Result<VBox<SnpGuestMsg>, u8>, Tracked<SnpPointsToRaw>))
    requires
        old(cs).inv(),
        len <= MAX_SNP_MSG_SZ,
        secret.wf_mastersecret(),
        payload_perm@.wf_default((payload_addr as int, len as nat)),
    ensures
        cs.inv(),
        ret.0.is_Ok() ==> ret.0.get_Ok_0().wf(),
        ret.0.is_Ok() ==> ret.0.get_Ok_0()@.is_constant(),
        ret.0.is_Ok() ==> ret.0.get_Ok_0().snp() === SwSnpMemAttr::spec_default(),
        payload_perm == ret.1@,
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid()]),
{
    let mut msg: VBox<SnpGuestMsg> = VBox::new_uninit(Tracked(cs));
    let mut snphdr: SnpGuestMsgHdr = msg.copy_snphdr();
    snphdr.algo = SNP_AEAD_AES_256_GCM.into();
    snphdr.hdr_version = MSG_HDR_VER.into();
    snphdr.hdr_sz = sizeof::<SnpGuestMsgHdr>().into();
    snphdr.msg_type = msg_type.into();
    snphdr.msg_version = version.into();
    snphdr.msg_seqno = msg_no.into();
    snphdr.msg_vmpck = VERISMO_VMPCK_ID.into();
    snphdr.msg_sz = len.into();
    assert(snphdr.is_constant());
    msg.set_snphdr(snphdr);
    let (msg, Tracked(payload_perm)) = enc_dec_payload(
        true,
        &secret.vmpck0,
        msg,
        msg_no.into(),
        payload_addr,
        Tracked(payload_perm),
    );
    (Ok(msg), Tracked(payload_perm))
}

} // verus!
verus! {

pub const SHA512_LEN2: usize = SHA512_LEN * 2;

pub fn cal2_sha512(input1: &SHA512Type, input2: &SHA512Type) -> (ret: SHA512Type)
    ensures
        ret === spec_cal_sha512((input1@ + input2@).vspec_cast_to()),
{
    let mut tmp_buf: Array<u8_s, SHA512_LEN2> = Default::default();
    let mut i = 0;
    while i < SHA512_LEN
        invariant
            0 <= i <= SHA512_LEN,
            forall|k: int| 0 <= k < i ==> tmp_buf[k] == input1[k],
            forall|k: int| 0 <= k < i ==> tmp_buf[k + SHA512_LEN] == input2[k],
    {
        tmp_buf.set2(i, *(input1.index2(i)));
        tmp_buf.set2(i + SHA512_LEN, *(input2.index2(i)));
        i = i + 1;
    }
    assert(tmp_buf@ =~~= input1@ + input2@);
    cal_sha512(&tmp_buf)
}

pub fn cal_sha512<T: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(buf: &T) -> (ret:
    SHA512Type)
    ensures
        ret === spec_cal_sha512(buf.vspec_cast_to()),
{
    let mut ret: SHA512Type = Default::default();
    trusted_cal_sha512(buf, &mut ret);
    ret
}

} // verus!
verus! {

impl SnpGuestChannel {
    pub fn attest(
        self,
        ghcb: GhcbHandle,
        secret: &SnpSecretsPageLayout,
        user_data: Array<u8_s, USER_DATA_LEN>,
        result: VBox<OnePage>,
        Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
    ) -> (ret: (VBox<OnePage>, Self, GhcbHandle))
        requires
            secret.wf_mastersecret(),
            result.wf(),
            result.snp() === SwSnpMemAttr::spec_default(),
            user_data.wf(),
            old(cs).inv(),
            ghcb.ghcb_wf(),
            self.wf(),
        ensures
            cs.inv(),
            cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_ALLOCATOR_lockid()]),
            ret.0.only_val_updated(result),
            ret.0.wf(),
            ret.1.wf(),
            ret.1.only_val_updated(self),
            ret.2.ghcb_wf(),
            ret.2.only_val_updated(ghcb),
    {
        proof {
            assert(set![spec_ALLOCATOR_lockid()].union(set![spec_ALLOCATOR_lockid()])
                =~~= set![spec_ALLOCATOR_lockid()]);
        }
        let mut req = self.req;
        let prev_msg_no: u64 = secret.os_area.msg_seqno_0.into();
        if prev_msg_no == MAXU64 {
            new_strlit(
                "msg_no is too large for vmpl communication. Please reset secret\n.",
            ).leak_debug();
            vc_terminate(SM_TERM_UNSUPPORTED, Tracked(&mut cs.snpcore));
        }
        let msg_no = (prev_msg_no + 1) as u64;
        let version = 1;
        let report_req = SnpReportReq { user_data, vmpl: 0, reserved: Array::new(0) };
        let ghost cs1 = *cs;
        let payload = VBox::<SnpReportReq>::new(report_req, Tracked(cs));
        let (payload_ptr, Tracked(payload_perm)) = payload.into_raw();
        let payload_addr = payload_ptr.to_usize();
        let ghost cs2 = *cs;
        let (encrypted, Tracked(payload_perm)) = enc_payload(
            secret,
            version,
            msg_no,
            SNP_GUEST_MSG_TYPE_REQ,
            payload_addr,
            size_of::<SnpReportReq>() as u16,
            Tracked(payload_perm.tracked_into_raw()),
            Tracked(cs),
        );
        let payload = VBox::<SnpReportReq>::from_raw(
            payload_addr,
            Tracked(payload_perm.tracked_into()),
        );
        if let Ok(encrypted) = encrypted {
            req = req.set(encrypted);
        } else {
            vc_terminate(SM_EVERCRYPT_EXIT, Tracked(&mut cs.snpcore));
        }
        let req_gpa = req.get_const_addr() as u64;
        let resp_gpa = self.resp.get_const_addr() as u64;
        let ghost cs3 = *cs;
        let ghcb = ghcb.ghcb_guest_request(req_gpa, resp_gpa, Tracked(cs));
        // Create a copy of private reponse message for verification.
        // This is necessary to avoid attacker skip the checking.
        let ghost cs4 = *cs;
        let mut private_resp = VBox::<SnpGuestMsg>::new_uninit(Tracked(cs));
        let (presp_ptr, Tracked(mut presp_perm)) = private_resp.into_raw();
        let (resp_ptr, Tracked(resp_perm)) = self.resp.into_raw();
        let tracked resp_perm = resp_perm.tracked_into_raw();
        let tracked mut presp_perm = presp_perm.tracked_into_raw();
        mem_copy(
            resp_ptr.to_usize(),
            presp_ptr.to_usize(),
            size_of::<SnpGuestMsg>(),
            Tracked(&resp_perm),
            Tracked(&mut presp_perm),
        );
        private_resp = VBox::from_raw(presp_ptr.to_usize(), Tracked(presp_perm.tracked_into()));
        let resp = VBox::from_raw(resp_ptr.to_usize(), Tracked(resp_perm.tracked_into()));
        let (rc, result, _) = verify_and_dec_payload(
            &secret.vmpck0,
            private_resp,
            msg_no,
            version,
            SNP_GUEST_MSG_TYPE_RESP,
            result,
        );
        if rc > 0 {
            vc_terminate(SM_EVERCRYPT_EXIT, Tracked(&mut cs.snpcore));
        }
        proof {
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
                *cs,
                set![],
                set![spec_ALLOCATOR_lockid()],
                set![],
                set![spec_ALLOCATOR_lockid()],
            );
        }
        (result, SnpGuestChannel { req, resp }, ghcb)
    }
}

} // verus!
verus! {

fn verify_and_dec_payload<T: IsConstant + SpecSize + WellFormed + VTypeCast<SecSeqByte>>(
    key: &AESKey256,
    msg: VBox<SnpGuestMsg>,
    old_msg_no: u64,
    version: u8,
    msg_type: u8,
    result: VBox<T>,
) -> (ret: (u8, VBox<T>, VBox<SnpGuestMsg>))
    requires
        old_msg_no < 0xffff_ffff_ffff_ffff,
        msg.snp() == SwSnpMemAttr::spec_default(),
        msg.wf(),
        msg@.is_constant(),
        key@.is_fullsecret(),
        result.wf(),
        result.snp() == SwSnpMemAttr::spec_default(),
    ensures
        ret.1.wf(),
        ret.2.wf(),
        ret.1.only_val_updated(result),
        ret.2.only_val_updated(msg),
{
    let expected_msg_no = old_msg_no + 1;
    let hdr = msg.borrow().snphdr;
    /* Verify that the sequence counter is incremented by 1 */
    let msg_no = hdr.msg_seqno.reveal_value();
    if msg_no != expected_msg_no {
        ((new_strlit("wrong seq number"), msg_no), expected_msg_no).leak_debug();
        return (SNP_ERR_REQ_RESP_MSG, result, msg);
    }  /* Verify response message type and version number. */

    if (msg_type != hdr.msg_type.reveal_value()) || (hdr.msg_version.reveal_value() != version) {
        new_strlit("wrong msg type").leak_debug();
        return (SNP_ERR_REQ_RESP_MSG, result, msg);
    }
    let msg_sz: usize = hdr.msg_sz.into();
    if msg_sz == 0 || msg_sz > (MAX_SNP_MSG_SZ as usize) || msg_sz >= size_of::<T>() {
        new_strlit("wrong msg size").leak_debug();
        return (SNP_ERR_REQ_RESP_MSG, result, msg);
    }
    let decrypted_addr = result.get_const_addr();
    let (decrypted_ptr, Tracked(decrypted_perm)) = result.into_raw();
    let tracked mut decrypted_perm = decrypted_perm.tracked_into_raw();
    let tracked (payload_perm, right_perm) = decrypted_perm.trusted_split(
        msg@.snphdr.spec_msg_sz().vspec_cast_to(),
    );
    /* Decrypt the payload */
    let (msg, Tracked(payload_perm)) = enc_dec_payload(
        false,
        key,
        msg,
        msg_no.into(),
        decrypted_addr,
        Tracked(payload_perm),
    );
    proof {
        decrypted_perm = payload_perm.trusted_join(right_perm);
    }
    (0, VBox::from_raw(decrypted_addr, Tracked(decrypted_perm.tracked_into())), msg)
}

} // verus!

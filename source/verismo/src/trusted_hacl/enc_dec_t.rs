use hacl_sys::*;

use super::*;

const AAD_LEN: usize = 48;
const IV_LEN: usize = 12;
const MAX_AUTHTAG_LEN: usize = 32;
const AES_256_KEY_LEN: usize = 32;

verismo_simple! {
pub type AESKey256 = [u8; AES_256_KEY_LEN];
pub type AESAuthTag = [u8; MAX_AUTHTAG_LEN];
pub type AESAddInfo = [u8; AAD_LEN];
pub type AESInv = [u8; IV_LEN];

/*
pub open spec fn ensures_encrypted_to<C: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(key: AESKey256, cipher: C, vmpl: nat) -> bool {
    key.sec_bytes().is_fullsecret_to(vmpl) ==> (cipher).sec_bytes().is_constant_to(vmpl)
}

pub open spec fn ensures_decrypted_to<P: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(key: AESKey256, plain: P, vmpl: nat) -> bool {
    key.sec_bytes().is_fullsecret_to(vmpl) ==> (plain).sec_bytes().is_fullsecret_to(vmpl)
}
*/
pub open spec fn ensures_encrypted_to(key: AESKey256, cipher: SecSeqByte, vmpl: nat) -> bool {
    &&& key@.is_fullsecret_to(vmpl) ==> (cipher).is_constant_to(vmpl)
    &&& cipher.wf()
}

// The decrypted messge might be secret or non-secret.
pub open spec fn ensures_decrypted_to(key: AESKey256, plain: SecSeqByte, vmpl: nat) -> bool {
    &&& key@.is_fullsecret_to(vmpl) ==> (plain).wf()
    &&& plain.wf()
}

/*
#[verifier(external_body)]
pub fn sev_encrypt<P: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>, C: IsConstant + WellFormed + SpecSize+ VTypeCast<SecSeqByte>>(
    key: &AESKey256,
    plain: &P,
    iv: &AESInv,
    ad: &AESAddInfo,
    tag: &AESAuthTag,
    cipher: &mut C,
) -> (ret: u8)
requires
    spec_size::<P>() == spec_size::<C>(),
ensures
    ensures_encrypted_to(*key, *cipher, 1),
    ensures_encrypted_to(*key, *cipher, 2),
    ensures_encrypted_to(*key, *cipher, 3),
    ensures_encrypted_to(*key, *cipher, 4),
{
    unsafe {
        // encrypt the plaintext
        EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
            key as *const _ as *mut u8,
            iv as *const _ as *mut u8,
            IV_LEN as u32,
            ad as *const _ as *mut u8,
            AAD_LEN as u32,
            plain as *const _ as *mut u8,
            size_of::<P>() as u32,
            cipher as *mut _ as *mut u8,
            tag as *const _ as *mut u8,
        )
    }
}

#[verifier(external_body)]
/// key: must be a secret
/// plain: could become not secret after decrypt if need_declass
pub fn sev_decrypt<P: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>, C: IsConstant + WellFormed + SpecSize + VTypeCast<SecSeqByte>>(
    key: &AESKey256,
    cipher: &C,
    iv: &AESInv,
    ad: &AESAddInfo,
    tag: &AESAuthTag,
    plain: &mut P,
) -> (ret: u8)
requires
    spec_size::<C>() == spec_size::<P>(),
ensures
    ensures_decrypted_to(*key, *plain, 1),
    ensures_decrypted_to(*key, *plain, 2),
    ensures_decrypted_to(*key, *plain, 3),
    ensures_decrypted_to(*key, *plain, 4),
{
    unsafe {
        // decrypt the plaintext
        EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
            key as *const _  as *mut u8,
            iv as *const _ as *mut u8,
            IV_LEN as u32,
            ad as *const _ as *mut u8,
            AAD_LEN as u32,
            cipher as *const _ as *mut u8,
            size_of::<C>() as u32,
            tag as *const _ as *mut u8,
            plain as *mut _ as *mut u8,
        )
    }
}
*/

#[verifier(external_body)]
pub fn raw_encrypt(
    key: &AESKey256,
    iv: &AESInv,
    ad: &AESAddInfo,
    tag: &AESAuthTag,
    len: u32_s,
    plain_addr: usize,
    cipher_addr: usize,
    Tracked(plain_perm): Tracked<&SnpPointsToRaw>,
    Tracked(cipher_perm): Tracked<&mut SnpPointsToRaw>,
) -> (ret: u8)
requires
    len == plain_perm@.size(),
    len == old(cipher_perm)@.size(),
ensures
    ensures_encrypted_to(*key, cipher_perm@.bytes(), 1),
    ensures_encrypted_to(*key, cipher_perm@.bytes(), 2),
    ensures_encrypted_to(*key, cipher_perm@.bytes(), 3),
    ensures_encrypted_to(*key, cipher_perm@.bytes(), 4),
    cipher_perm@.only_val_updated(old(cipher_perm)@),
{
    unsafe {
        // encrypt the plaintext
        EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
            key as *const _ as *mut u8,
            iv as *const _ as *mut u8,
            IV_LEN as u32,
            ad as *const _ as *mut u8,
            AAD_LEN as u32,
            plain_addr as *mut u8,
            len.into(),
            cipher_addr as *mut u8,
            tag as *const _ as *mut u8,
        )
    }
}

#[verifier(external_body)]
/// key: must be a secret
/// plain: could become not secret after decrypt if need_declass
pub fn raw_decrypt(
    key: &AESKey256,
    iv: &AESInv,
    ad: &AESAddInfo,
    tag: &AESAuthTag,
    len: u32_s,
    plain_addr: usize,
    cipher_addr: usize,
    Tracked(plain_perm): Tracked<&mut SnpPointsToRaw>,
    Tracked(cipher_perm): Tracked<&SnpPointsToRaw>,
) -> (ret: u8)
requires
    len == old(plain_perm)@.size(),
    len == cipher_perm@.size(),
ensures
    ensures_decrypted_to(*key, plain_perm@.bytes(), 1),
    ensures_decrypted_to(*key, plain_perm@.bytes(), 2),
    ensures_decrypted_to(*key, plain_perm@.bytes(), 3),
    ensures_decrypted_to(*key, plain_perm@.bytes(), 4),
    plain_perm@.only_val_updated(old(plain_perm)@),
{
    unsafe {
        // decrypt the plaintext
        EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
            key as *const _  as *mut u8,
            iv as *const _ as *mut u8,
            IV_LEN as u32,
            ad as *const _ as *mut u8,
            AAD_LEN as u32,
            cipher_addr as *mut u8,
            len.into(),
            tag as *const _ as *mut u8,
            plain_addr as *mut u8,
        )
    }
}

}

use super::*;

verismo! {
    pub type SHA512Type = [u8; SHA512_LEN];
}

verus! {

pub const SHA512_LEN: usize = { 512 / 8 };

pub open spec fn spec_cal_sha512(input: SecSeqByte) -> SHA512Type;

} // verus!

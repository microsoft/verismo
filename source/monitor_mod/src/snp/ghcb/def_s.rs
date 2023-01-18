use super::*;

verus! {
pub const GHCB_BUFFER_SIZE: usize = 0x7f0;

#[derive(PartialEq, Eq, SpecIntEnum)]
pub enum SvmStatus {
    Ok = 0,
    Unsupported,  /* Requested operation not supported */
    VmmError,     /* Unexpected state from the VMM */
    DecodeFailed, /* Instruction decoding failed */
    Exception,    /* Instruction caused exception */
    Retry,        /* Retry instruction emulation */
}
}
verismo! {
pub struct GHCBProto;
}

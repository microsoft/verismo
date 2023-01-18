use verismo_macro::*;

use crate::arch::addr_s::*;
use crate::arch::crypto::{CryptoMask, Encrypted, SymKey};
use crate::arch::entities::*;
use crate::tspec::*;

pub type MemKey = SymKey<(ASID, int)>;

pub type EncryptedByte = Encrypted<MemKey, Byte>;

verus!{
#[derive(SpecGetter, SpecSetter)]
pub struct RamDB {
    pub data: Seq<EncryptedByte>,
    pub write_count: int,
    pub crypto_mask: Seq<CryptoMask>,
}
}

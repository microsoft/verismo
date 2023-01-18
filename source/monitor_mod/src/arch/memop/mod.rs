mod gpmemop;
mod gvmemop;
mod memop;

use verismo_macro::*;

use crate::arch::entities::*;
use crate::arch::rmp::RmpOp;
use crate::tspec::*;

verus!{
#[is_variant]
/// Memory Operation for GVA, GPA, and SPA.
/// When AddrT = GuestVir, encrypt: bool is not unused and so just set it to false by default
pub enum MemOp<AddrT> {
    Read(AddrMemID<AddrT>, bool),           // addr, encrypt
    Write(AddrID<AddrT>, bool, ByteStream), // addr, encrypt, content to write,
    InvlPage(AddrMemID<AddrT>),
    FlushAll(MemID),
    RmpOp(RmpOp<AddrT>),
}
}
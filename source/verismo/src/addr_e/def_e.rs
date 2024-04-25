use super::*;
use crate::debug::VPrint;

verus! {

pub open spec fn VM_MEM_RANGE() -> (int, nat) {
    (0, VM_MEM_SIZE as nat)
}

} // verus!
verismo! {
pub type VPage = usize;
pub type PPage = usize;
pub type VAddr = usize;
pub type PAddr = usize;

pub type OnePage = [u8; 0x1000];
}

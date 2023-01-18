use super::*;

verus! {
pub const VMPL_COUNT: usize = 4;
pub const BSP: u64 = 0;
}

#[macro_export]
macro_rules! RICHOS_VMPL {
    () => {
        crate::arch::VMPL::VMPL1
    };
}

verismo_simple! {
pub type StackPages = [u8; 0x4000];
}

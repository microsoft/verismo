use alloc::alloc::Layout;

use super::*;
use crate::global::*;
use crate::lock::VSpinLock;

#[verifier::external]
pub fn verismo_size(layout: &Layout) -> usize {
    if layout.size() < 16 {
        16
    } else {
        layout.size()
    }
}

#[verifier::external]
unsafe impl core::alloc::GlobalAlloc for VSpinLock<VeriSMoAllocator> {
    #[verifier::external]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let res = self.alloc_aligned(
            verismo_size(&layout),
            layout.align(),
            Tracked::assume_new(),
            Tracked::assume_new(),
        );
        if res.is_ok() {
            res.unwrap().0 as *mut u8
        } else {
            0 as *mut u8
        }
    }

    #[verifier::external]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.dealloc_(
            ptr as usize,
            verismo_size(&layout),
            Tracked::assume_new(),
            Tracked::assume_new(),
            Tracked::assume_new(),
        );
    }
}

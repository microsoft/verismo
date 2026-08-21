//! Ghost-only checks pinning concrete architectural values against the named
//! constants, so a mistyped bit fails verification instead of silently changing
//! the model. The `by (bit_vector)` steps are needed because the solver does not
//! evaluate masks of `bitflags` views on its own.
use vstd::prelude::*;

use machine_model::arch::x86_64::{Cr0Value, EferValue};

use super::reg_contract::{cr0_paging_precondition, efer_paging_precondition};

verus! {

proof fn cr0_paging_precondition_holds_for_concrete_value() {
    let cr0 = Cr0Value::from_bits_retain(0x8001_0011);
    assert(cr0@ == 0x8001_0011u64);
    assert((0x8001_0011u64 & 0x1u64) == 0x1u64) by (bit_vector);
    assert((0x8001_0011u64 & 0x8000_0000u64) == 0x8000_0000u64) by (bit_vector);
    assert((0x8001_0011u64 & 0x1_0000u64) == 0x1_0000u64) by (bit_vector);
    assert((0x8001_0011u64 & 0x2000_0000u64) != 0x2000_0000u64) by (bit_vector);
    assert(cr0_paging_precondition(cr0));
}

proof fn efer_paging_precondition_holds_for_concrete_value() {
    let efer = EferValue::from_bits_retain(0xD00);
    assert((0xD00u64 & 0x100u64) == 0x100u64) by (bit_vector);
    assert((0xD00u64 & 0x400u64) == 0x400u64) by (bit_vector);
    assert(efer_paging_precondition(efer));
}

} // verus!

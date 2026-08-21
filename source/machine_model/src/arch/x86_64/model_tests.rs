//! Ghost-only checks pinning concrete architectural values against the named
//! constants, so a mistyped bit fails verification instead of silently changing
//! the model. The `by (bit_vector)` steps are needed because the solver does not
//! evaluate masks of `bitflags` views on its own.
use vstd::prelude::*;

use crate::arch::x86_64::RflagsValue;

verus! {

proof fn with_alignment_check_sets_only_ac() {
    let rflags = RflagsValue::from_bits_retain(0x246);
    assert(rflags.with_alignment_check(true)@ == 0x4_0246u64) by {
        assert((0x246u64 | 0x4_0000u64) == 0x4_0246u64) by (bit_vector);
    }
    assert(rflags.with_alignment_check(false)@ == 0x246u64) by {
        assert((0x246u64 & !0x4_0000u64) == 0x246u64) by (bit_vector);
    }
}

proof fn io_privilege_level_decodes_the_field() {
    let ring0 = RflagsValue::from_bits_retain(0x246);
    assert(ring0.io_privilege_level() == 0u8) by {
        assert(((0x246u64 & 0x3000u64) >> 12u64) == 0u64) by (bit_vector);
    }
    let ring3 = RflagsValue::from_bits_retain(0x3246);
    assert(ring3.io_privilege_level() == 3u8) by {
        assert(((0x3246u64 & 0x3000u64) >> 12u64) == 3u64) by (bit_vector);
    }
}

} // verus!

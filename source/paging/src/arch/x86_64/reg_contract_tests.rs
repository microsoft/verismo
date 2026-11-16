//! Checks pinning concrete architectural values against the named constants, so
//! a mistyped bit fails verification instead of silently changing the model,
//! plus an exec example showing how a control-register write is discharged
//! against the contract. The `by (bit_vector)` steps are needed because the
//! solver does not evaluate masks of `bitflags` views on its own.
use vstd::prelude::*;

use machine_model::arch::x86_64::state::RegisterState;
use machine_model::arch::x86_64::{cpl, Cr0Value, Cr4, Cr4Value, EferValue};

use super::reg_contract::{cr0_paging_precondition, efer_paging_precondition, paging_inv};
use crate::structs::arch_contract::ArchPagingGeometry;

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

/// Example of exec code driving a control-register update while holding the
/// tracked register state: setting `CR4.SMEP` leaves every paging control bit
/// alone, so `PagingRegisters::inv` is re-established after the write.
fn enable_smep<A: ArchPagingGeometry>(Tracked(regs): Tracked<&mut RegisterState>)
    requires
        paging_inv::<A>(old(regs)),
        cpl(old(regs).cs.value()) == 0,
    ensures
        paging_inv::<A>(final(regs)),
        final(regs).cr4.value().contains(Cr4Value::SMEP),
{
    let cr4 = Cr4.read(Tracked(&regs.cs), Tracked(&mut regs.rflags), Tracked(&regs.cr4));
    let new_cr4 = cr4.union(Cr4Value::SMEP);
    Cr4.write(new_cr4, Tracked(&regs.cs), Tracked(&mut regs.rflags), Tracked(&mut regs.cr4));
    proof {
        let old_bits = cr4@;
        let new_bits = new_cr4@;
        assert(new_bits == (old_bits | 0x10_0000u64));
        assert((old_bits | 0x10_0000u64) & 0x10_0000u64 == 0x10_0000u64) by (bit_vector);
        assert((old_bits | 0x10_0000u64) & 0x20u64 == old_bits & 0x20u64) by (bit_vector);
        assert((old_bits | 0x10_0000u64) & 0x2_0000u64 == old_bits & 0x2_0000u64) by (bit_vector);
        assert((old_bits | 0x10_0000u64) & 0x1000u64 == old_bits & 0x1000u64) by (bit_vector);
    }
}

} // verus!

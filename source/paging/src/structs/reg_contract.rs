//! The architectural preconditions the register state must satisfy for the page
//! tables to have their intended meaning.
use vstd::prelude::*;

use machine_model::arch::x86_64::state::RegisterState;
use machine_model::arch::x86_64::{Cr0Value, Cr3Value, Cr4Value, EferValue};

use super::arch_contract::{geometry_wf, ArchPagingGeometry};

verus! {

// ---------------------------------------------------------------------------
// EFER (MSR 0xC000_0080)
// ---------------------------------------------------------------------------
/// The MSR number for EFER.
pub const MSR_EFER: u32 = 0xC000_0080;

/// The typed reading of the raw `u64` held by the EFER MSR token: every MSR
/// token carries a `u64`, so the flags view is built here rather than stored.
pub open spec fn efer_value(registers: &RegisterState) -> EferValue {
    EferValue::from_bits_retain(registers.msrs.index(MSR_EFER).value())
}

// ---------------------------------------------------------------------------
// Architectural preconditions
// ---------------------------------------------------------------------------
pub open spec fn cr0_paging_precondition(cr0: Cr0Value) -> bool {
    &&& cr0.contains(Cr0Value::PE)
    &&& cr0.contains(Cr0Value::PG)
    &&& cr0.contains(Cr0Value::WP)
    &&& (cr0.contains(Cr0Value::NW) ==> cr0.contains(Cr0Value::CD))
}

/// Requires the bits above the physical address width to be clear, plus, when
/// PCID is disabled, the low 12 bits other than `PWT`/`PCD`.
pub open spec fn cr3_paging_precondition<A: ArchPagingGeometry>(
    cr3: Cr3Value,
    cr4: Cr4Value,
) -> bool {
    &&& (cr3@ & !(low_bits_mask_u64(A::phys_addr_width()))) == 0
    &&& !cr3.intersects(Cr3Value::NOFLUSH)
    &&& (!cr4.contains(Cr4Value::PCIDE) ==> (cr3@ & (low_bits_mask_u64(A::page_offset_width()) & !(
    Cr3Value::PWT@ | Cr3Value::PCD@))) == 0)
}

pub open spec fn cr4_paging_precondition(cr0: Cr0Value, cr4: Cr4Value, efer: EferValue) -> bool {
    &&& cr4.contains(Cr4Value::PAE)
    &&& (cr4.contains(Cr4Value::PCIDE) ==> cr0.contains(Cr0Value::PG) && efer.contains(
        EferValue::LMA,
    ))
    &&& (cr4.contains(Cr4Value::LA57) ==> efer.contains(EferValue::LMA))
}

pub open spec fn efer_paging_precondition(efer: EferValue) -> bool {
    &&& efer.contains(EferValue::LME)
    &&& efer.contains(EferValue::LMA)
}

pub open spec fn cpl_precondition(cpl: u64) -> bool {
    cpl <= 3
}

/// `u64`-typed variant of `vstd::bits::low_bits_mask`.
pub open spec fn low_bits_mask_u64(n: nat) -> u64 {
    (vstd::bits::low_bits_mask(n) as u64)
}

// ---------------------------------------------------------------------------
// PagingView
// ---------------------------------------------------------------------------
/// The paging-relevant values held by the register state, gathered into one
/// value so that paging contracts do not have to borrow `RegisterState`.
pub ghost struct PagingView {
    pub cr0: Cr0Value,
    pub cr3: Cr3Value,
    pub cr4: Cr4Value,
    pub efer: EferValue,
    pub cpl: u64,
}

pub open spec fn paging_view(registers: &RegisterState) -> PagingView {
    PagingView {
        cr0: registers.cr0.value(),
        cr3: registers.cr3.value(),
        cr4: registers.cr4.value(),
        efer: efer_value(registers),
        cpl: registers.cpl.value(),
    }
}

pub open spec fn paging_inv<A: ArchPagingGeometry>(registers: &RegisterState) -> bool {
    &&& registers.msrs.dom().contains(MSR_EFER)
    &&& paging_view(registers).inv::<A>()
}

impl PagingView {
    pub open spec fn inv<A: ArchPagingGeometry>(&self) -> bool {
        &&& geometry_wf::<A>()
        &&& cr0_paging_precondition(self.cr0)
        &&& cr3_paging_precondition::<A>(self.cr3, self.cr4)
        &&& cr4_paging_precondition(self.cr0, self.cr4, self.efer)
        &&& efer_paging_precondition(self.efer)
        &&& cpl_precondition(self.cpl)
    }
}

} // verus!

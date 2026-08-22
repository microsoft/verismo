//! The architectural preconditions the register state must satisfy for the page
//! tables to have their intended meaning.
//!
//! Trusted. Every clause below is transcribed from the vendor manuals:
//! AMD64 Architecture Programmer's Manual, Volume 2: System Programming
//! (referred to as "APM Vol. 2"), and Intel 64 and IA-32 Architectures Software
//! Developer's Manual, Volume 3A (referred to as "SDM Vol. 3A"). The two agree
//! on all of the paging control bits used here, so the contract is stated once
//! rather than per vendor.
use core::marker::PhantomData;

use vstd::prelude::*;

use machine_model::arch::x86_64::state::RegisterState;
use machine_model::arch::x86_64::{Cr0Value, Cr3Value, Cr4Value, EferValue};

use crate::structs::arch_contract::{page_offset_width, ArchPagingGeometry};
use crate::structs::sizes::PageOffset;

verus! {

// ---------------------------------------------------------------------------
// EFER (MSR 0xC000_0080)
// ---------------------------------------------------------------------------
/// The MSR number for EFER (APM Vol. 2, "Extended Feature Enable Register
/// (EFER)"; SDM Vol. 3A calls it `IA32_EFER`).
pub const MSR_EFER: u32 = 0xC000_0080;

/// The typed reading of the raw `u64` held by the EFER MSR token: every MSR
/// token carries a `u64`, so the flags view is built here rather than stored.
pub open spec fn efer_value(registers: &RegisterState) -> EferValue {
    EferValue::from_bits_retain(registers.msrs.index(MSR_EFER).value())
}

// ---------------------------------------------------------------------------
// Architectural preconditions
// ---------------------------------------------------------------------------
/// CR0 bits required for paging: protected mode enabled, paging enabled, and
/// supervisor writes honouring read-only mappings. `NW` without `CD` is a
/// reserved combination that faults on load.
///
/// APM Vol. 2, "CR0 Register"; SDM Vol. 3A, "Control Registers".
pub open spec fn cr0_paging_precondition(cr0: Cr0Value) -> bool {
    &&& cr0.contains(Cr0Value::PE)
    &&& cr0.contains(Cr0Value::PG)
    &&& cr0.contains(Cr0Value::WP)
    &&& (cr0.contains(Cr0Value::NW) ==> cr0.contains(Cr0Value::CD))
}

/// Requires the bits above the physical address width to be clear, plus, when
/// PCID is disabled, the low 12 bits other than `PWT`/`PCD`. Bit 63 selects the
/// no-flush form of a `MOV to CR3`, which is only defined while `CR4.PCIDE` is
/// set, so it is required clear here.
///
/// APM Vol. 2, "CR3 Register" and the long-mode CR3 formats; SDM Vol. 3A,
/// "4-Level Paging and 5-Level Paging" (CR3 field tables).
pub open spec fn cr3_paging_precondition<A: ArchPagingGeometry>(
    cr3: Cr3Value,
    cr4: Cr4Value,
) -> bool {
    &&& (cr3@ & !(low_bits_mask_u64(A::phys_addr_width()))) == 0
    &&& !cr3.intersects(Cr3Value::NOFLUSH)
    &&& (!cr4.contains(Cr4Value::PCIDE) ==> (cr3@ & (low_bits_mask_u64(page_offset_width::<A>())
        & !(Cr3Value::PWT@ | Cr3Value::PCD@))) == 0)
}

/// CR4 bits constrained in every paging mode: `PCIDE` and `LA57` are only
/// architecturally settable once long mode is active. Which mode is in effect
/// is [`PagingView::level_count`]'s business.
///
/// APM Vol. 2, "CR4 Register" and "Enabling Long Mode"; SDM Vol. 3A, "Control
/// Registers" and "Initializing IA-32e Mode".
pub open spec fn cr4_paging_precondition(cr0: Cr0Value, cr4: Cr4Value, efer: EferValue) -> bool {
    &&& (cr4.contains(Cr4Value::PCIDE) ==> cr0.contains(Cr0Value::PG) && efer.contains(
        EferValue::LMA,
    ))
    &&& (cr4.contains(Cr4Value::LA57) ==> efer.contains(EferValue::LMA))
}

/// Long mode is both enabled (`LME`) and active (`LMA`). The processor sets
/// `LMA` itself once `LME` and `CR0.PG` are both set with `CR4.PAE`.
///
/// APM Vol. 2, "Enabling Long Mode"; SDM Vol. 3A, "Initializing IA-32e Mode".
pub open spec fn efer_paging_precondition(efer: EferValue) -> bool {
    &&& efer.contains(EferValue::LME)
    &&& efer.contains(EferValue::LMA)
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
pub ghost struct PagingView<A: ArchPagingGeometry> {
    pub cr0: Cr0Value,
    pub cr3: Cr3Value,
    pub cr4: Cr4Value,
    pub efer: EferValue,
    pub cs: u16,
    pub arch: PhantomData<A>,
}

pub open spec fn paging_view<A: ArchPagingGeometry>(registers: &RegisterState) -> PagingView<A> {
    PagingView {
        cr0: registers.cr0.value(),
        cr3: registers.cr3.value(),
        cr4: registers.cr4.value(),
        efer: efer_value(registers),
        cs: registers.cs.value(),
        arch: PhantomData,
    }
}

pub open spec fn paging_inv<A: ArchPagingGeometry>(registers: &RegisterState) -> bool {
    &&& registers.msrs.dom().contains(MSR_EFER)
    &&& paging_view::<A>(registers).inv()
}

impl<A: ArchPagingGeometry> PagingView<A> {
    /// The registers have to select the very tree `A` describes: how deep the
    /// hardware walks is a paging mode, and `CR3` names the root of a tree of
    /// that depth, so a mismatch would let a table be read at the wrong level.
    ///
    /// Every mode maps 4 KiB pages at the leaf, which is also what makes
    /// `CR3`'s low bits the ones `cr3_paging_precondition` reserves.
    pub open spec fn mode_precondition(&self) -> bool {
        &&& A::MinPageSize::SHIFT == 12
        &&& self.level_precondition()
    }

    /// How deep the hardware walks, as the mode bits select it: `PAE` without
    /// long mode adds a third level to 32-bit paging, and `LA57` adds a fifth
    /// to long mode's four.
    ///
    /// APM Vol. 2, "Legacy-Mode Page Translation", "Long-Mode Page Translation"
    /// and "5-Level Address Translation"; SDM Vol. 3A, "32-Bit Paging", "PAE
    /// Paging" and "4-Level Paging and 5-Level Paging".
    pub open spec fn level_count(&self) -> nat {
        if !self.efer.contains(EferValue::LMA) {
            if self.cr4.contains(Cr4Value::PAE) {
                3nat
            } else {
                2nat
            }
        } else if self.cr4.contains(Cr4Value::LA57) {
            5nat
        } else {
            4nat
        }
    }

    pub open spec fn level_precondition(&self) -> bool {
        self.level_count() == A::root_depth() + 1
    }

    pub open spec fn inv(&self) -> bool {
        &&& cr0_paging_precondition(self.cr0)
        &&& cr3_paging_precondition::<A>(self.cr3, self.cr4)
        &&& cr4_paging_precondition(self.cr0, self.cr4, self.efer)
        &&& self.mode_precondition()
        &&& efer_paging_precondition(self.efer)
    }
}

} // verus!

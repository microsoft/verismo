use vstd::prelude::*;

use crate::register::*;

verus! {

/// Spec-only helper computing the value of a single bit. Used instead of raw shift
/// expressions so bit positions are self-documenting; `n` is always a small
/// compile-time constant in this module, so this never approaches the `u64` shift
/// width limit.
pub open spec fn bit(n: u64) -> u64 {
    1u64 << n
}

// ---------------------------------------------------------------------------
// CR0
// ---------------------------------------------------------------------------
/// CR0.PE (Protection Enable), bit 0.
pub const CR0_PE: u64 = 0x1;

/// CR0.WP (Write Protect), bit 16.
pub const CR0_WP: u64 = 0x1_0000;

/// CR0.NW (Not Write-through), bit 29.
pub const CR0_NW: u64 = 0x2000_0000;

/// CR0.CD (Cache Disable), bit 30.
pub const CR0_CD: u64 = 0x4000_0000;

/// CR0.PG (Paging Enable), bit 31.
pub const CR0_PG: u64 = 0x8000_0000;

// ---------------------------------------------------------------------------
// CR3
// ---------------------------------------------------------------------------
/// CR3.PWT (Page-level Write-Through), bit 3.
pub const CR3_PWT: u64 = 0x8;

/// CR3.PCD (Page-level Cache Disable), bit 4.
pub const CR3_PCD: u64 = 0x10;

/// Modeled physical-address width, in bits.
pub const PHYS_ADDR_WIDTH: u64 = 52;

/// Width of the in-page byte offset, in bits (4KB pages).
pub const PAGE_OFFSET_WIDTH: u64 = 12;

/// Modeled physical *page number* width, in bits: the physical address width
/// minus the page offset bits. Physical page numbers are bounded by
/// `1 << PHYS_PAGE_NUMBER_WIDTH`.
pub const PHYS_PAGE_NUMBER_WIDTH: u64 = (PHYS_ADDR_WIDTH - PAGE_OFFSET_WIDTH) as u64;

/// CR3 bit 63: the `MOV to CR3` "no-flush" control. This is write-only: it is
/// consumed by the write operation itself and never persists as architectural
/// state, so it must always read back as clear. This is documented explicitly
/// even though it is also excluded by the high-bit reserved mask in
/// `cr3_paging_precondition`, since the write-only semantics (rather than mere
/// reservedness) is the reason it must be clear.
pub const CR3_NOFLUSH: u64 = 0x8000_0000_0000_0000;

// ---------------------------------------------------------------------------
// CR4
// ---------------------------------------------------------------------------
/// CR4.PAE (Physical Address Extension), bit 5.
pub const CR4_PAE: u64 = 0x20;

/// CR4.LA57 (57-bit linear addresses), bit 12.
pub const CR4_LA57: u64 = 0x1000;

/// CR4.PCIDE (Process-Context Identifiers Enable), bit 17.
pub const CR4_PCIDE: u64 = 0x2_0000;

/// CR4.SMEP (Supervisor Mode Execution Prevention), bit 20.
pub const CR4_SMEP: u64 = 0x10_0000;

/// CR4.SMAP (Supervisor Mode Access Prevention), bit 21.
pub const CR4_SMAP: u64 = 0x20_0000;

/// CR4.PKE (Protection Key Enable), bit 22.
pub const CR4_PKE: u64 = 0x40_0000;

// ---------------------------------------------------------------------------
// EFER (MSR 0xC000_0080)
// ---------------------------------------------------------------------------
/// The MSR number for EFER.
pub const MSR_EFER: u32 = 0xC000_0080;

/// EFER.LME (Long Mode Enable), bit 8.
pub const EFER_LME: u64 = 0x100;

/// EFER.LMA (Long Mode Active), bit 10.
pub const EFER_LMA: u64 = 0x400;

/// EFER.NXE (No-Execute Enable), bit 11.
pub const EFER_NXE: u64 = 0x800;

// ---------------------------------------------------------------------------
// RFLAGS
// ---------------------------------------------------------------------------
/// RFLAGS bit 1: architecturally fixed to 1 (reserved).
pub const RFLAGS_FIXED1: u64 = 0x2;

/// RFLAGS.AC (Alignment Check), bit 18.
pub const RFLAGS_AC: u64 = 0x4_0000;

// ---------------------------------------------------------------------------
// Ghost page mappings
// ---------------------------------------------------------------------------
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub ghost struct PageMapping {
    pub physical_page: u64,
    pub writable: bool,
    pub executable: bool,
    pub user: bool,
    pub protection_key: u8,
}

pub type PageMappings = Map<u64, PageMapping>;

impl PageMapping {
    /// A single mapping is well-formed with respect to the current EFER value:
    /// the physical page number fits the modeled physical page-number width
    /// (`PHYS_PAGE_NUMBER_WIDTH`, derived from the 52-bit physical address width
    /// minus the 12-bit page offset, i.e. `< 1 << 40`), the protection key is a
    /// valid 4-bit index, and non-executable mappings are only meaningful when
    /// `EFER.NXE` is set (otherwise the NX bit is reserved and every mapping is
    /// architecturally executable).
    ///
    /// `protection_key` is modeled unconditionally, independent of `CR4.PKE`:
    /// when PKE is clear, hardware ignores the protection key entirely (any
    /// stored value is simply inert), so this predicate does not need `cr4` and
    /// does not require `protection_key == 0` in that mode. `CR4.PKE` (along
    /// with `SMEP`, `SMAP`, and `RFLAGS.AC`) is retained in the register state
    /// for a later access-check relation (deciding whether a given access is
    /// permitted), not for static mapping validity as checked here.
    pub open spec fn inv(self, efer: u64) -> bool {
        &&& self.physical_page < (1u64 << PHYS_PAGE_NUMBER_WIDTH)
        &&& self.protection_key < 16
        &&& (self.executable || (efer & EFER_NXE) != 0)
    }
}

// ---------------------------------------------------------------------------
// Architectural preconditions
// ---------------------------------------------------------------------------
/// CR0 must have PE, PG and WP set, and NW must imply CD.
pub open spec fn cr0_paging_precondition(cr0: u64) -> bool {
    &&& (cr0 & CR0_PE) != 0
    &&& (cr0 & CR0_PG) != 0
    &&& (cr0 & CR0_WP) != 0
    &&& ((cr0 & CR0_NW) != 0 ==> (cr0 & CR0_CD) != 0)
}

/// CR3 must not use the modeled-reserved bits above the physical address width
/// (including the write-only no-flush bit 63), and when PCID is disabled the low
/// 12 bits other than PWT/PCD must be zero.
pub open spec fn cr3_paging_precondition(cr3: u64, cr4: u64) -> bool {
    &&& (cr3 & !(low_bits_mask_u64(PHYS_ADDR_WIDTH as nat))) == 0
    &&& (cr3 & CR3_NOFLUSH) == 0
    &&& ((cr4 & CR4_PCIDE) == 0 ==> (cr3 & (low_bits_mask_u64(12) & !(CR3_PWT | CR3_PCD))) == 0)
}

/// CR4 must have PAE set; PCIDE implies paging is enabled and long mode is
/// active; LA57 implies long mode is active.
pub open spec fn cr4_paging_precondition(cr0: u64, cr4: u64, efer: u64) -> bool {
    &&& (cr4 & CR4_PAE) != 0
    &&& ((cr4 & CR4_PCIDE) != 0 ==> (cr0 & CR0_PG) != 0 && (efer & EFER_LMA) != 0)
    &&& ((cr4 & CR4_LA57) != 0 ==> (efer & EFER_LMA) != 0)
}

/// EFER must have LME and LMA set; NXE is optional.
pub open spec fn efer_paging_precondition(efer: u64) -> bool {
    &&& (efer & EFER_LME) != 0
    &&& (efer & EFER_LMA) != 0
}

/// RFLAGS must have the architecturally fixed bit 1 set; AC is optional.
pub open spec fn rflags_precondition(rflags: u64) -> bool {
    (rflags & RFLAGS_FIXED1) != 0
}

/// CPL must be a valid privilege level (0..=3).
pub open spec fn cpl_precondition(cpl: u64) -> bool {
    cpl <= 3
}

/// `u64`-typed variant of `vstd::bits::low_bits_mask`, usable directly as a bit
/// mask in the spec expressions above.
pub open spec fn low_bits_mask_u64(n: nat) -> u64 {
    (vstd::bits::low_bits_mask(n) as u64)
}

// ---------------------------------------------------------------------------
// PageTableGlobalState
// ---------------------------------------------------------------------------
/// The aggregated global paging state: a ghost view of the paging-relevant
/// architectural state. The register tokens themselves are owned by
/// `RegisterState`; this structure only carries the ghost mapping of virtual
/// page numbers to page mappings implied by the current page tables, and
/// relates it to a borrowed `RegisterState` through `inv`.
pub ghost struct PageTableGlobalState {
    pub mappings: PageMappings,
}

impl PageTableGlobalState {
    /// The global invariant, relative to the register state: the register state
    /// is itself well-formed and owns the EFER MSR token, the register values
    /// satisfy all x86-64 paging architectural preconditions, and every ghost
    /// page mapping is well-formed with respect to the current EFER value.
    pub open spec fn inv(&self, registers: &RegisterState) -> bool {
        &&& registers.inv()
        &&& registers.msrs.dom().contains(MSR_EFER)
        &&& cr0_paging_precondition(registers.cr0.value())
        &&& cr3_paging_precondition(registers.cr3.value(), registers.cr4.value())
        &&& cr4_paging_precondition(
            registers.cr0.value(),
            registers.cr4.value(),
            registers.msrs[MSR_EFER].value(),
        )
        &&& efer_paging_precondition(registers.msrs[MSR_EFER].value())
        &&& rflags_precondition(registers.rflags.value())
        &&& cpl_precondition(registers.cpl.value())
        &&& forall|va: u64|
            #![trigger self.mappings.dom().contains(va)]
            self.mappings.dom().contains(va) ==> self.mappings[va].inv(
                registers.msrs[MSR_EFER].value(),
            )
    }
}

} // verus!

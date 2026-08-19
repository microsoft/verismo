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
    /// CR3 bit 63: the `MOV to CR3` "no-flush" control. This is write-only: it is
    /// consumed by the write operation itself and never persists as architectural
    /// state, so it must always read back as clear.
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
        /// the physical page number fits the modeled physical address width (with a
        /// 12-bit page offset, i.e. `< 1 << 40` for a 52-bit physical address space),
        /// the protection key is a valid 4-bit index, and non-executable mappings are
        /// only meaningful when `EFER.NXE` is set (otherwise the NX bit is reserved
        /// and every mapping is architecturally executable).
        pub open spec fn inv(self, efer: u64) -> bool {
            &&& self.physical_page < (1u64 << 40)
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

    /// PKRU is a 32-bit register; the upper 32 bits must be zero.
    pub open spec fn pkru_precondition(pkru: u64) -> bool {
        (pkru & !(low_bits_mask_u64(32))) == 0
    }

    /// `u64`-typed variant of `vstd::bits::low_bits_mask`, usable directly as a bit
    /// mask in the spec expressions above.
    pub open spec fn low_bits_mask_u64(n: nat) -> u64 {
        (vstd::bits::low_bits_mask(n) as u64)
    }

    // ---------------------------------------------------------------------------
    // Checked value extractors
    // ---------------------------------------------------------------------------

    /// Extract the CR0 value from a `RegisterValue`, or `None` if it isn't a CR0 value.
    pub open spec fn extract_cr0(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Cr0(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the CR2 value from a `RegisterValue`, or `None` if it isn't a CR2 value.
    pub open spec fn extract_cr2(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Cr2(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the CR3 value from a `RegisterValue`, or `None` if it isn't a CR3 value.
    pub open spec fn extract_cr3(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Cr3(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the CR4 value from a `RegisterValue`, or `None` if it isn't a CR4 value.
    pub open spec fn extract_cr4(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Cr4(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the EFER value from a `RegisterValue`, or `None` if it isn't the EFER
    /// MSR (register number `MSR_EFER`).
    pub open spec fn extract_efer(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::MSR { register, value } if register == MSR_EFER => Some(value),
            _ => None,
        }
    }

    /// Extract the RFLAGS value from a `RegisterValue`, or `None` if it isn't an
    /// RFLAGS value.
    pub open spec fn extract_rflags(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Rflags(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the CPL value from a `RegisterValue`, or `None` if it isn't a CPL
    /// value.
    pub open spec fn extract_cpl(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Cpl(v) => Some(v),
            _ => None,
        }
    }

    /// Extract the PKRU value from a `RegisterValue`, or `None` if it isn't a PKRU
    /// value.
    pub open spec fn extract_pkru(value: RegisterValue) -> Option<u64> {
        match value {
            RegisterValue::Pkru(v) => Some(v),
            _ => None,
        }
    }

    // ---------------------------------------------------------------------------
    // PageTableGlobalState
    // ---------------------------------------------------------------------------

    /// The aggregated global paging state: tracked ownership tokens for every
    /// register that participates in the x86-64 paging architecture, plus the
    /// ghost mapping of virtual page numbers to page mappings implied by the
    /// current page tables.
    pub tracked struct PageTableGlobalState {
        pub tracked cr0: RegisterPointsTo,
        pub tracked cr2: RegisterPointsTo,
        pub tracked cr3: RegisterPointsTo,
        pub tracked cr4: RegisterPointsTo,
        pub tracked efer: RegisterPointsTo,
        pub tracked rflags: RegisterPointsTo,
        pub tracked cpl: RegisterPointsTo,
        pub tracked pkru: RegisterPointsTo,
        pub ghost mappings: PageMappings,
    }

    impl PageTableGlobalState {
        pub closed spec fn cr0_value(&self) -> Option<u64> {
            extract_cr0(self.cr0.value())
        }

        pub closed spec fn cr2_value(&self) -> Option<u64> {
            extract_cr2(self.cr2.value())
        }

        pub closed spec fn cr3_value(&self) -> Option<u64> {
            extract_cr3(self.cr3.value())
        }

        pub closed spec fn cr4_value(&self) -> Option<u64> {
            extract_cr4(self.cr4.value())
        }

        pub closed spec fn efer_value(&self) -> Option<u64> {
            extract_efer(self.efer.value())
        }

        pub closed spec fn rflags_value(&self) -> Option<u64> {
            extract_rflags(self.rflags.value())
        }

        pub closed spec fn cpl_value(&self) -> Option<u64> {
            extract_cpl(self.cpl.value())
        }

        pub closed spec fn pkru_value(&self) -> Option<u64> {
            extract_pkru(self.pkru.value())
        }

        /// The global invariant: every register token holds a value of the exact
        /// expected register identity (with EFER additionally pinned to the exact
        /// MSR number), the decoded values satisfy all x86-64 paging architectural
        /// preconditions, and every ghost page mapping is well-formed with respect
        /// to the current EFER value.
        pub open spec fn inv(&self) -> bool {
            &&& self.cr0_value().is_some()
            &&& self.cr2_value().is_some()
            &&& self.cr3_value().is_some()
            &&& self.cr4_value().is_some()
            &&& self.efer_value().is_some()
            &&& self.rflags_value().is_some()
            &&& self.cpl_value().is_some()
            &&& self.pkru_value().is_some()
            &&& cr0_paging_precondition(self.cr0_value().unwrap())
            &&& cr3_paging_precondition(self.cr3_value().unwrap(), self.cr4_value().unwrap())
            &&& cr4_paging_precondition(
                self.cr0_value().unwrap(),
                self.cr4_value().unwrap(),
                self.efer_value().unwrap(),
            )
            &&& efer_paging_precondition(self.efer_value().unwrap())
            &&& rflags_precondition(self.rflags_value().unwrap())
            &&& cpl_precondition(self.cpl_value().unwrap())
            &&& pkru_precondition(self.pkru_value().unwrap())
            &&& forall|va: u64|
                #![trigger self.mappings.dom().contains(va)]
                self.mappings.dom().contains(va)
                    ==> self.mappings[va].inv(self.efer_value().unwrap())
        }
    }

    #[cfg(feature = "verification-test")]
    mod verification_test {
        use super::*;

        proof fn check_bit_constants() {
            assert(CR0_PE == 1);
            assert(CR0_WP == bit(16)) by (bit_vector);
            assert(CR0_NW == bit(29)) by (bit_vector);
            assert(CR0_CD == bit(30)) by (bit_vector);
            assert(CR0_PG == bit(31)) by (bit_vector);

            assert(CR3_PWT == bit(3)) by (bit_vector);
            assert(CR3_PCD == bit(4)) by (bit_vector);
            assert(CR3_NOFLUSH == bit(63)) by (bit_vector);

            assert(CR4_PAE == bit(5)) by (bit_vector);
            assert(CR4_LA57 == bit(12)) by (bit_vector);
            assert(CR4_PCIDE == bit(17)) by (bit_vector);
            assert(CR4_SMEP == bit(20)) by (bit_vector);
            assert(CR4_SMAP == bit(21)) by (bit_vector);
            assert(CR4_PKE == bit(22)) by (bit_vector);

            assert(EFER_LME == bit(8)) by (bit_vector);
            assert(EFER_LMA == bit(10)) by (bit_vector);
            assert(EFER_NXE == bit(11)) by (bit_vector);

            assert(RFLAGS_FIXED1 == bit(1)) by (bit_vector);
            assert(RFLAGS_AC == bit(18)) by (bit_vector);

            assert(MSR_EFER == 0xC000_0080);
        }

        proof fn check_cr0_precondition() {
            assert((CR0_PE | CR0_PG | CR0_WP) & CR0_PE != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP) & CR0_PG != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP) & CR0_WP != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP) & CR0_NW == 0) by (bit_vector);
            assert(cr0_paging_precondition(CR0_PE | CR0_PG | CR0_WP));
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW | CR0_CD) & CR0_PE != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW | CR0_CD) & CR0_PG != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW | CR0_CD) & CR0_WP != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW | CR0_CD) & CR0_CD != 0) by (bit_vector);
            assert(cr0_paging_precondition(CR0_PE | CR0_PG | CR0_WP | CR0_NW | CR0_CD));
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW) & CR0_NW != 0) by (bit_vector);
            assert((CR0_PE | CR0_PG | CR0_WP | CR0_NW) & CR0_CD == 0) by (bit_vector);
            assert(!cr0_paging_precondition(CR0_PE | CR0_PG | CR0_WP | CR0_NW));
            assert((CR0_PG | CR0_WP) & CR0_PE == 0) by (bit_vector);
            assert(!cr0_paging_precondition(CR0_PG | CR0_WP));
        }

        proof fn check_efer_precondition() {
            assert((EFER_LME | EFER_LMA) & EFER_LME != 0) by (bit_vector);
            assert((EFER_LME | EFER_LMA) & EFER_LMA != 0) by (bit_vector);
            assert(efer_paging_precondition(EFER_LME | EFER_LMA));
            assert((EFER_LME | EFER_LMA | EFER_NXE) & EFER_LME != 0) by (bit_vector);
            assert((EFER_LME | EFER_LMA | EFER_NXE) & EFER_LMA != 0) by (bit_vector);
            assert(efer_paging_precondition(EFER_LME | EFER_LMA | EFER_NXE));
            assert(EFER_LME & EFER_LMA == 0) by (bit_vector);
            assert(!efer_paging_precondition(EFER_LME));
        }

        proof fn check_cr4_precondition() {
            let cr0 = CR0_PE | CR0_PG | CR0_WP;
            let efer = EFER_LME | EFER_LMA;
            assert((CR0_PE | CR0_PG | CR0_WP) & CR0_PG != 0) by (bit_vector);
            assert(CR4_PAE & CR4_PAE != 0) by (bit_vector);
            assert(CR4_PAE & CR4_PCIDE == 0) by (bit_vector);
            assert(CR4_PAE & CR4_LA57 == 0) by (bit_vector);
            assert((EFER_LME | EFER_LMA) & EFER_LMA != 0) by (bit_vector);
            assert(cr4_paging_precondition(cr0, CR4_PAE, efer));
            assert((CR4_PAE | CR4_PCIDE) & CR4_PAE != 0) by (bit_vector);
            assert((CR4_PAE | CR4_PCIDE) & CR4_PCIDE != 0) by (bit_vector);
            assert(cr4_paging_precondition(cr0, CR4_PAE | CR4_PCIDE, efer));
            assert(EFER_LME & EFER_LMA == 0) by (bit_vector);
            assert(!cr4_paging_precondition(cr0, CR4_PAE | CR4_PCIDE, EFER_LME));
            assert((CR4_PAE | CR4_LA57) & CR4_LA57 != 0) by (bit_vector);
            assert(!cr4_paging_precondition(cr0, CR4_PAE | CR4_LA57, EFER_LME));
            assert(0u64 & CR4_PAE == 0) by (bit_vector);
            assert(!cr4_paging_precondition(cr0, 0, efer));
        }

        proof fn check_cpl_precondition() {
            assert(cpl_precondition(0));
            assert(cpl_precondition(3));
            assert(!cpl_precondition(4));
        }

        proof fn check_pkru_precondition() {
            vstd::bits::lemma_low_bits_mask_values();
            assert(low_bits_mask_u64(32) == 0xFFFF_FFFF);
            assert(0u64 & !(0xFFFF_FFFFu64) == 0) by (bit_vector);
            assert(pkru_precondition(0));
            assert(0xFFFF_FFFFu64 & !(0xFFFF_FFFFu64) == 0) by (bit_vector);
            assert(pkru_precondition(0xFFFF_FFFF));
            assert(0x1_0000_0000u64 & !(0xFFFF_FFFFu64) != 0) by (bit_vector);
            assert(!pkru_precondition(0x1_0000_0000));
        }

        proof fn check_rflags_precondition() {
            assert(RFLAGS_FIXED1 & RFLAGS_FIXED1 != 0) by (bit_vector);
            assert(rflags_precondition(RFLAGS_FIXED1));
            assert((RFLAGS_FIXED1 | RFLAGS_AC) & RFLAGS_FIXED1 != 0) by (bit_vector);
            assert(rflags_precondition(RFLAGS_FIXED1 | RFLAGS_AC));
            assert(0u64 & RFLAGS_FIXED1 == 0) by (bit_vector);
            assert(!rflags_precondition(0));
        }

        proof fn check_extractors_exact() {
            assert(extract_cr0(RegisterValue::Cr0(5)) == Some(5u64));
            assert(extract_cr0(RegisterValue::Cr3(5)) is None);

            assert(extract_efer(RegisterValue::MSR { register: MSR_EFER, value: 7 }) == Some(7u64));
            assert(extract_efer(RegisterValue::MSR { register: 1, value: 7 }) is None);
            assert(extract_efer(RegisterValue::Cr0(1)) is None);
        }

        proof fn check_page_mapping_inv() {
            let efer_nxe = EFER_LME | EFER_LMA | EFER_NXE;
            let efer_no_nxe = EFER_LME | EFER_LMA;

            let exec_mapping = PageMapping {
                physical_page: 0,
                writable: true,
                executable: true,
                user: false,
                protection_key: 0,
            };
            assert((1u64 << 40) == 0x100_0000_0000u64) by (bit_vector);
            assert(exec_mapping.physical_page < 0x100_0000_0000u64);
            assert(exec_mapping.inv(efer_no_nxe));
            assert(exec_mapping.inv(efer_nxe));

            let noexec_mapping = PageMapping {
                physical_page: 0,
                writable: true,
                executable: false,
                user: false,
                protection_key: 0,
            };
            assert(noexec_mapping.physical_page < 0x100_0000_0000u64);
            assert((EFER_LME | EFER_LMA | EFER_NXE) & EFER_NXE != 0) by (bit_vector);
            assert(noexec_mapping.inv(efer_nxe));
            assert((EFER_LME | EFER_LMA) & EFER_NXE == 0) by (bit_vector);
            assert(!noexec_mapping.inv(efer_no_nxe));
        }
    }
}

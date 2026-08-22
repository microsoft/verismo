use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use crate::address::{Address, PhysAddr};
use crate::sizes::{PageOffset, PageSize};
use bitflags::Flags;
use bitflags_verus::FlagsSpec;
use builtin_macros::verus_verify;

use crate::structs::entry::PTEntry;

/// Executable interface to a page table entry's flag word.
///
/// Kept in plain Rust, annotated rather than rewritten, so the flag types can
/// be shared with unverified code. Its ghost half is
/// [`GenericPageTableFlagsSpec`].
#[verus_verify]
pub trait GenericPageTableFlags:
    bitflags::Flags<Bits = usize>
    + core::ops::BitAnd<Output = Self>
    + core::ops::BitOr<Output = Self>
    + Copy
    + Clone
{
    const PRESENT: Self;

    const USER: Self;

    const HUGE: Self;

    /// Default flags for newly created parent page table entries.
    ///
    /// These flags must be permissive enough to form a superset of all
    /// possible descendant leaf entry permissions, since effective access
    /// rights are constrained by both parent and leaf entries.
    fn parent_flags() -> Self;

    /// Flags for the self-map entry itself. This may differ from `parent_flags`
    fn self_map_table_flags() -> Self;

    #[verus_spec(ret =>
        ensures
            Self::obeys_bitflags_spec() ==> ret == self.contains_spec(Self::HUGE),
    )]
    fn huge(&self) -> bool {
        self.contains(Self::HUGE)
    }

    #[verus_spec(ret =>
        ensures
            Self::obeys_bitflags_spec() ==> ret == self.contains_spec(Self::PRESENT),
    )]
    fn present(&self) -> bool {
        self.contains(Self::PRESENT)
    }

    #[verus_spec(ret =>
        ensures
            Self::obeys_bitflags_spec() ==> ret == self.contains_spec(Self::USER),
    )]
    fn user(&self) -> bool {
        self.contains(Self::USER)
    }
}

verus! {

/// The address geometry a host supplies. Split out of `ArchPagingMeta` so that
/// specifications can be stated against it without depending on the executable
/// entry-manipulation half of that trait.
pub trait ArchPagingGeometry: Sized {
    /// Smallest page this architecture can map. Its shift is the width of the
    /// in-page byte offset.
    type MinPageSize: PageSize;

    spec fn phys_addr_width() -> nat;

    /// Sanity condition on the geometry, discharged by the host so that callers
    /// need not carry it as a precondition.
    proof fn lemma_geometry_wf()
        ensures
            <Self::MinPageSize as PageOffset>::SHIFT < Self::phys_addr_width() <= 64,
    ;
}

/// Width of the in-page byte offset, in bits.
pub open spec fn page_offset_width<A: ArchPagingGeometry>() -> nat {
    <A::MinPageSize as PageOffset>::SHIFT as nat
}

/// Number of virtual-address bits one paging level consumes: enough to index
/// every entry of a table page.
pub open spec fn level_index_width<A: ArchPagingMeta>() -> nat {
    log(2, PTEntry::<A>::count_per_page() as int) as nat
}

/// Shift of the page a level maps: `depth` levels above the leaf, each level
/// covering `level_index_width` more address bits.
pub open spec fn level_shift<A: ArchPagingMeta>(depth: nat) -> nat {
    (page_offset_width::<A>() + depth * level_index_width::<A>()) as nat
}

/// Address of a table page's entry `index`. Stated once here so that no
/// specification has to spell out the entry stride.
pub open spec fn slot_addr<A: ArchPagingMeta>(base: usize, index: int) -> int {
    base as int + index * vstd::layout::size_of::<PTEntry<A>>()
}

/// Whether the level geometry fits the entry width: a table page's entries are
/// indexed by a whole number of address bits, and the tree spans no more bits
/// than an address has.
///
/// Stated as a predicate rather than a trait obligation because it is defined
/// in terms of `PTEntry<A>`, which is itself indexed by `A`: naming it
/// inside `ArchPagingMeta` would be a cyclic definition. Each architecture
/// instantiates and discharges it.
pub open spec fn level_geometry_wf<A: ArchPagingMeta>() -> bool {
    &&& pow2(level_index_width::<A>()) == PTEntry::<A>::count_per_page()
    &&& 0 < level_index_width::<A>() < 64
}

/// The ghost half of [`GenericPageTableFlags`]: which bit each named flag
/// occupies, and the well-formedness the entry encoding relies on.
///
/// Separate from the exec trait so that a flag type can be defined -- and used
/// by unverified code -- without carrying proofs, and so that the bit positions
/// are named in one place that specifications can refer to.
pub trait GenericPageTableFlagsSpec: GenericPageTableFlags {
    /// Every bit a named flag can occupy. Bits outside the address field may
    /// fall outside this too, since a flag whose position the machine reports
    /// at runtime -- the C-bit -- cannot be a constant of the architecture.
    spec fn spec_all_bits() -> usize;

    spec fn spec_present_bit() -> usize;

    spec fn spec_huge_bit() -> usize;

    spec fn spec_user_bit() -> usize;

    /// Executable mirrors of the bit positions above. The associated consts of
    /// [`GenericPageTableFlags`] cannot serve here: Verus gives an associated
    /// const no ghost value unless its initializer is a bare name, which a
    /// `bitflags`-generated flag never is.
    fn present_bit() -> (ret: usize)
        ensures
            ret == Self::spec_present_bit(),
    ;

    fn huge_bit() -> (ret: usize)
        ensures
            ret == Self::spec_huge_bit(),
    ;

    fn user_bit() -> (ret: usize)
        ensures
            ret == Self::spec_user_bit(),
    ;

    proof fn lemma_flag_bits_wf()
        ensures
            Self::obeys_bitflags_spec(),
            Self::spec_present_bit() != 0,
            Self::spec_huge_bit() != 0,
            Self::spec_present_bit() & Self::spec_huge_bit() == 0,
            Self::spec_present_bit() & Self::spec_all_bits() == Self::spec_present_bit(),
            Self::spec_huge_bit() & Self::spec_all_bits() == Self::spec_huge_bit(),
            Self::spec_user_bit() & Self::spec_all_bits() == Self::spec_user_bit(),
    ;
}

pub trait ArchPagingMeta: 'static + Copy + ArchPagingGeometry {
    type PTFlags: GenericPageTableFlagsSpec;

    /// Spec-level mirror of `private_pte_mask()`.
    spec fn spec_private_mask() -> usize;

    /// Spec-level mirror of `shared_pte_mask()`.
    spec fn spec_shared_mask() -> usize;

    /// Spec-level mirror of `address_mask()`.
    spec fn spec_address_mask() -> usize;

    /// Sanity conditions relating the masks above, discharged once per
    /// architecture rather than carried as a precondition by every caller.
    proof fn lemma_pte_masks_wf()
        ensures
            Self::PTFlags::spec_present_bit() != 0,
            Self::PTFlags::spec_huge_bit() != 0,
            Self::PTFlags::spec_present_bit() & Self::PTFlags::spec_huge_bit() == 0,
            Self::spec_address_mask() & Self::PTFlags::spec_present_bit() == 0,
            Self::spec_address_mask() & Self::PTFlags::spec_huge_bit() == 0,
            Self::spec_private_mask() & Self::spec_shared_mask() == 0,
            // No named flag overlaps the address field, so assembling an
            // entry from an address and flags loses neither.
            Self::PTFlags::spec_all_bits() & !Self::spec_address_mask()
                == Self::PTFlags::spec_all_bits(),
    ;

    /// Returns the bitmask ORed into physical addresses for private
    /// (encrypted) page table entries.
    fn private_pte_mask() -> (ret: usize)
        ensures
            ret == Self::spec_private_mask(),
    ;

    /// Returns the bitmask ORed into physical addresses for shared
    /// (plaintext) page table entries.
    fn shared_pte_mask() -> (ret: usize)
        ensures
            ret == Self::spec_shared_mask(),
    ;

    /// Physical address mask.
    /// x64 supports 52-bit physical addresses, so the mask is usually 0x000f_ffff_ffff_f000.
    fn address_mask() -> (ret: usize)
        ensures
            ret == Self::spec_address_mask(),
    ;

    /// Returns a bitmask of PTEntryFlags that the hardware supports.
    ///
    /// Override this method to filter unsupported bits (e.g., `GLOBAL` before CR4.PGE is enabled)
    /// so that they are silently cleared. The default allows all flags.
    fn supported_flags() -> Self::PTFlags;

    /// Clears the private encryption bit(s) from `paddr`.
    fn strip_confidentiality_bits(paddr: PhysAddr) -> PhysAddr {
        (paddr.bits() & !Self::private_pte_mask()).into()
    }

    /// Clears the shared bit(s) from `paddr`.
    fn strip_shared_address_bits(paddr: PhysAddr) -> PhysAddr {
        (paddr.bits() & !Self::shared_pte_mask()).into()
    }

    /// Returns `paddr` with the private encryption mask applied.
    ///
    /// Any shared bits are stripped first so the result is exclusively
    /// private.
    fn make_private_address(paddr: PhysAddr) -> PhysAddr {
        (Self::strip_shared_address_bits(paddr).bits() | Self::private_pte_mask()).into()
    }

    /// Returns `paddr` with the shared mask applied.
    ///
    /// Any confidentiality (private) bits are stripped first so the result
    /// is exclusively shared.
    fn make_shared_address(paddr: PhysAddr) -> PhysAddr {
        (Self::strip_confidentiality_bits(paddr).bits() | Self::shared_pte_mask()).into()
    }

    /// Returns `true` if `paddr` already has the shared mask applied.
    fn is_shared_address(paddr: PhysAddr) -> bool {
        paddr == Self::make_shared_address(paddr)
    }
}

} // verus!

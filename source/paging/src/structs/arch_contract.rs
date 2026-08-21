use vstd::prelude::*;

use crate::address::{Address, PhysAddr};
use crate::sizes::{PageOffset, PageSize};

verus! {

/// The address geometry a host supplies. Split out of `ArchPagingMeta` so that
/// specifications can be stated against it without depending on the executable
/// entry-manipulation half of that trait.
pub trait ArchPagingGeometry: Sized {
    /// Smallest page this architecture can map. Its shift is the width of the
    /// in-page byte offset.
    type MinPageSize: PageSize;

    spec fn phys_addr_width() -> nat;

    /// Number of virtual-address bits one paging level consumes, so a table page
    /// holds `1 << level_index_width()` entries.
    spec fn level_index_width() -> nat;

    /// Number of paging levels, counting the leaf level that maps `MinPageSize`.
    spec fn level_count() -> nat;

    /// Sanity condition on the geometry, discharged by the host so that callers
    /// need not carry it as a precondition.
    proof fn lemma_geometry_wf()
        ensures
            <Self::MinPageSize as PageOffset>::SHIFT < Self::phys_addr_width() <= 64,
            0 < Self::level_index_width() < 64,
            0 < Self::level_count(),
            <Self::MinPageSize as PageOffset>::SHIFT + Self::level_count()
                * Self::level_index_width() <= 64,
    ;
}

/// Width of the in-page byte offset, in bits.
pub open spec fn page_offset_width<A: ArchPagingGeometry>() -> nat {
    <A::MinPageSize as PageOffset>::SHIFT as nat
}

/// Shift of the page a level maps: `depth` levels above the leaf, each level
/// covering `level_index_width` more address bits.
pub open spec fn level_shift<A: ArchPagingGeometry>(depth: nat) -> nat {
    (page_offset_width::<A>() + depth * A::level_index_width()) as nat
}

pub trait GenericPageTableFlags: bitflags::Flags<Bits = usize> + core::ops::BitAnd<
    Output = Self,
> + core::ops::BitOr<Output = Self> + Copy + Clone {
    const PRESENT: Self;

    const USER: Self;

    const HUGE: Self;

    /// Default flags for newly created parent page table entries.
    ///
    /// These flags must be permissive enough to form a superset of all
    /// possible descendant leaf entry permissions, since effective access
    /// rights are constrained by both parent and leaf entries.
    fn parent_flags() -> Self;

    /// The raw bits `present()`/`huge()` are read from. `bitflags::Flags` has
    /// no Verus-visible spec for a generic implementer, so an architecture
    /// states its own bit pattern here rather than through `.bits()`.
    spec fn spec_bits(&self) -> usize;

    /// Spec-level mask tested by `present()`. Paired with `spec_bits` so
    /// entry-level specs can state presence without decoding `Self`.
    spec fn spec_present_bit() -> usize;

    /// Spec-level mask tested by `huge()`.
    spec fn spec_huge_bit() -> usize;

    fn huge(&self) -> (ret: bool)
        ensures
            ret == (self.spec_bits() & Self::spec_huge_bit() != 0),
    ;

    fn present(&self) -> (ret: bool)
        ensures
            ret == (self.spec_bits() & Self::spec_present_bit() != 0),
    ;

    /// Raw value of the `PRESENT` bit, so a caller assembling a fresh raw
    /// word does not need a `Self` value just to read a constant.
    fn present_bit() -> (ret: usize)
        ensures
            ret == Self::spec_present_bit(),
    ;

    /// Raw value of the `HUGE` bit.
    fn huge_bit() -> (ret: usize)
        ensures
            ret == Self::spec_huge_bit(),
    ;

    /// Spec-level mask tested by `user()`.
    spec fn spec_user_bit() -> usize;

    fn user(&self) -> (ret: bool)
        ensures
            ret == (self.spec_bits() & Self::spec_user_bit() != 0),
    ;
}

pub trait ArchPagingMeta: 'static + Copy + ArchPagingGeometry {
    type PTFlags: GenericPageTableFlags;

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

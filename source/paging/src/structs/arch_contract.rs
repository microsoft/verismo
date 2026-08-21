use vstd::prelude::*;

use crate::address::{Address, PhysAddr};

verus! {

/// The address geometry a host supplies. Split out of `ArchPagingMeta` so that
/// specifications can be stated against it without depending on the executable
/// entry-manipulation half of that trait.
pub trait ArchPagingGeometry {
    spec fn phys_addr_width() -> nat;

    spec fn page_offset_width() -> nat;
}

/// Sanity condition on a host's geometry. Stated here rather than left to the
/// host, so that a host cannot weaken it.
pub open spec fn geometry_wf<A: ArchPagingGeometry>() -> bool {
    0 < A::page_offset_width() < A::phys_addr_width() <= 64
}

} // verus!

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

    fn huge(&self) -> bool {
        self.contains(Self::HUGE)
    }

    fn present(&self) -> bool {
        self.contains(Self::PRESENT)
    }

    fn user(&self) -> bool {
        self.contains(Self::USER)
    }
}

pub trait ArchPagingMeta: 'static + Copy + ArchPagingGeometry {
    const PAGE_SIZE: usize;
    type PTFlags: GenericPageTableFlags;

    /// Returns the bitmask ORed into physical addresses for private
    /// (encrypted) page table entries.
    fn private_pte_mask() -> usize;

    /// Returns the bitmask ORed into physical addresses for shared
    /// (plaintext) page table entries.
    fn shared_pte_mask() -> usize;

    /// Physical address mask.
    /// x64 supports 52-bit physical addresses, so the mask is usually 0x000f_ffff_ffff_f000.
    fn address_mask() -> usize;

    /// Returns a bitmask of PTEntryFlags that the hardware supports.
    ///
    /// Override this method to filter unsupported bits (e.g., `GLOBAL` before CR4.PGE is enabled)
    /// so that they are silently cleared. The default allows all flags.
    fn supported_flags() -> Self::PTFlags {
        <Self::PTFlags as bitflags::Flags>::all()
    }

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
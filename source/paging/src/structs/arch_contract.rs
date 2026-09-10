//! What an architecture owes the page table: the layout of an entry's flag
//! word, and where in an entry's address field the confidentiality tags sit.
use bitflags::Flags;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::tlb::TlbFlush;

/// A page table entry's flag word.
pub trait GenericPageTableFlags:
    Flags<Bits = usize>
    + core::ops::BitAnd<Output = Self>
    + core::ops::BitOr<Output = Self>
    + Copy
    + Clone
{
    const PRESENT: Self;

    const WRITABLE: Self;

    const USER: Self;

    const HUGE: Self;

    /// Flags for a newly created parent entry. They must be permissive enough
    /// to cover every descendant leaf, since effective access rights are the
    /// intersection of a leaf's and its ancestors'.
    fn parent_flags() -> Self;

    /// Flags for the self-map entry itself, which may differ from
    /// [`Self::parent_flags`].
    fn self_map_table_flags() -> Self;

    /// The union of two flag words.
    fn with(self, other: Self) -> Self {
        Self::from_bits_retain(self.bits() | other.bits())
    }

    /// `self` with every flag of `other` cleared. Splitting a large mapping
    /// needs it: the pieces inherit the permissions of the entry they came
    /// from, but not its size bit.
    fn without(self, other: Self) -> Self {
        Self::from_bits_retain(self.bits() & !other.bits())
    }

    fn huge(&self) -> bool {
        self.contains(Self::HUGE)
    }

    fn present(&self) -> bool {
        self.contains(Self::PRESENT)
    }

    fn user(&self) -> bool {
        self.contains(Self::USER)
    }

    fn present_bit() -> usize {
        Self::PRESENT.bits()
    }

    fn huge_bit() -> usize {
        Self::HUGE.bits()
    }

    fn writable_bit() -> usize {
        Self::WRITABLE.bits()
    }

    fn user_bit() -> usize {
        Self::USER.bits()
    }
}

/// Architecture-specific page table metadata for confidential computing: which
/// address bits mark a page private or shared, both zero where memory is not
/// encrypted. Implementers are markers that are never instantiated.
pub trait ArchPagingMeta: 'static + Copy {
    type PTFlags: GenericPageTableFlags;

    /// What a mutation of this architecture's tables owes the TLB.
    type TlbFlushTok: TlbFlush;

    /// The bits ORed into a physical address for a private (encrypted) entry.
    fn private_pte_mask() -> usize;

    /// The bits ORed into a physical address for a shared (plaintext) entry.
    fn shared_pte_mask() -> usize;

    /// Physical address mask; x86-64 supports 52-bit addresses, so this is
    /// usually `0x000f_ffff_ffff_f000`.
    fn address_mask() -> usize;

    /// Flags the hardware supports. Override to silently clear bits that are
    /// not yet legal, such as `GLOBAL` before CR4.PGE is enabled.
    fn supported_flags() -> Self::PTFlags {
        Self::PTFlags::all()
    }

    fn strip_confidentiality_bits(paddr: PhysAddr) -> PhysAddr {
        (paddr.bits() & !Self::private_pte_mask()).into()
    }

    fn strip_shared_address_bits(paddr: PhysAddr) -> PhysAddr {
        (paddr.bits() & !Self::shared_pte_mask()).into()
    }

    /// `paddr` marked private. Shared bits are stripped first, so the result is
    /// exclusively private.
    fn make_private_address(paddr: PhysAddr) -> PhysAddr {
        (Self::strip_shared_address_bits(paddr).bits() | Self::private_pte_mask()).into()
    }

    /// `paddr` marked shared, private bits stripped first.
    fn make_shared_address(paddr: PhysAddr) -> PhysAddr {
        (Self::strip_confidentiality_bits(paddr).bits() | Self::shared_pte_mask()).into()
    }

    fn is_shared_address(paddr: PhysAddr) -> bool {
        paddr == Self::make_shared_address(paddr)
    }
}

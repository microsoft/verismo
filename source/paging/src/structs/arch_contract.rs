//! What an architecture owes the page table: the layout of an entry's flag
//! word, and where in an entry's address field the confidentiality tags sit.
use bitflags::Flags;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::level::PageLevel;
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
    const PRESENT_BIT: usize;

    const WRITABLE: Self;
    const WRITABLE_BIT: usize;

    const USER: Self;
    const USER_BIT: usize;

    const HUGE: Self;
    const HUGE_BIT: usize;

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

    #[inline(always)]
    fn present_bit() -> usize {
        Self::PRESENT_BIT
    }

    #[inline(always)]
    fn huge_bit() -> usize {
        Self::HUGE_BIT
    }

    #[inline(always)]
    fn writable_bit() -> usize {
        Self::WRITABLE_BIT
    }

    #[inline(always)]
    fn user_bit() -> usize {
        Self::USER_BIT
    }
}

/// Architecture-specific page table metadata for confidential computing: which
/// address bits mark a page private or shared, both zero where memory is not
/// encrypted. Implementers are markers that are never instantiated.
pub trait ArchPagingMeta: 'static + Copy {
    /// The architecture's typed page-table flag word.
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

    /// Attribute bits that overlap the address/huge fields and must be
    /// preserved or relocated when a leaf at `level` is split one level down.
    fn split_leaf_attributes(_entry: usize, _level: PageLevel) -> usize {
        0
    }

    /// Leaf attributes that are not permissions, such as x86 PAT.
    fn leaf_attribute_mask(_level: PageLevel) -> usize {
        0
    }

    /// Hardware-maintained history retained when changing permissions.
    /// Without `use_ad`, all these bits are preset on every present entry;
    /// include every hardware A/D bit, without address or permission bits.
    /// Presetting them must be valid for both table pointers and leaf mappings.
    fn accessed_dirty_mask() -> usize {
        0
    }

    /// Whether replacing this valid descriptor with another valid descriptor
    /// requires invalidation and completed TLB maintenance before publication.
    fn requires_break_before_make(old: usize, new: usize, level: PageLevel) -> bool;

    /// Declared flags allowed in new mapping/protection requests, for example
    /// excluding `GLOBAL` before CR4.PGE is enabled. Structural bits and
    /// preserved attributes remain governed by the operation's page level.
    fn supported_flags() -> Self::PTFlags {
        Self::PTFlags::all()
    }

    /// Filter optional flags, retaining structural bits and unnamed extensions.
    fn filter_flags(flags: Self::PTFlags) -> Self::PTFlags {
        let structural = Self::PTFlags::present_bit() | Self::PTFlags::huge_bit();
        let disabled = Self::PTFlags::all().bits() & !Self::supported_flags().bits() & !structural;
        Self::PTFlags::from_bits_retain(flags.bits() & !disabled)
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

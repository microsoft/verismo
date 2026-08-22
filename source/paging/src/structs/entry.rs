//! Encoding of a single hardware page-table entry: what its bits mean, and
//! the small algebra (`entry_step`) a lock-free walker relies on once a slot
//! has been observed to hold a table pointer.
//!
//! Type definitions and their specs only -- no walking, no mapping, no
//! allocation. Nothing here knows which level an entry is read at: at the leaf
//! level bit 7 is PAT rather than PS, so it is the walk layer, which knows the
//! page's depth, that must refuse to descend below the leaf.
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::arch_contract::{
    ArchPagingMeta, GenericPageTableFlags, GenericPageTableFlagsSpec,
};
use bitflags::Flags;
use bitflags_verus::FlagsSpec;

use crate::structs::sizes::PageSize;

verus! {

/// A single hardware page-table entry: a raw machine word, typed by the
/// architecture whose bit layout it follows.
///
/// Carries no invariant of its own -- a page-table page is exactly
/// `count_per_page()` of these, freshly zeroed or freshly read off hardware, so
/// any `usize` (garbage included) is a well-formed value. What each bit
/// *means* is stated by the spec functions below, in terms of the masks
/// `ArchPagingMeta` supplies.
#[repr(transparent)]
pub struct PTEntry<A: ArchPagingMeta> {
    val: usize,
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PTEntry<A> {
    /// How many entries a table page holds: a table page is one page of the
    /// architecture's smallest size, filled with entries.
    pub open spec fn count_per_page() -> nat {
        (<A::MinPageSize as PageSize>::SIZE as nat) / vstd::layout::size_of::<Self>()
    }

    /// Raw word.
    pub closed spec fn view(&self) -> usize {
        self.val
    }

    #[verifier::when_used_as_spec(view)]
    pub fn raw(&self) -> (ret: usize)
        returns
            self.view(),
    {
        self.val
    }

    /// Whether the entry is the null word, which is what an unused slot holds.
    pub open spec fn is_clear_spec(&self) -> bool {
        self.view() == 0
    }

    #[verifier::when_used_as_spec(is_clear_spec)]
    pub fn is_clear(&self) -> (ret: bool)
        returns
            self.is_clear_spec(),
    {
        self.val == 0
    }

    pub fn clear(&mut self)
        ensures
            final(self).is_clear_spec(),
    {
        self.val = 0;
    }

    /// The entry a raw word denotes. The protocol layer reads and writes slots
    /// as plain words, so it needs both directions of this correspondence.
    pub closed spec fn spec_from_bits(val: usize) -> Self {
        Self { val, dummy: PhantomData }
    }

    #[verifier::when_used_as_spec(spec_from_bits)]
    pub fn from_bits(val: usize) -> (ret: Self)
        ensures
            ret == Self::spec_from_bits(val),
            ret.view() == val,
    {
        Self { val, dummy: PhantomData }
    }

    /// Encoding and decoding are inverses. Both directions are `closed`, so a
    /// layer that stores entries as plain words needs this stated.
    pub proof fn lemma_bits_roundtrip(entry: Self)
        ensures
            Self::spec_from_bits(entry.view()) == entry,
    {
    }

    /// Decoding a word and reading it back gives the word.
    pub proof fn lemma_view_of_bits(val: usize)
        ensures
            Self::spec_from_bits(val).view() == val,
    {
    }

    /// The address-field bits, *including* any confidentiality/shared tag
    /// the architecture stores alongside the physical address (SVSM's
    /// `paddr_field`). This is the value a table entry keeps fixed once
    /// installed -- see `entry_step`.
    pub open spec fn paddr_field_spec(&self) -> usize {
        self.view() & A::spec_address_mask()
    }

    #[verifier::when_used_as_spec(paddr_field_spec)]
    pub fn paddr_field(&self) -> (ret: usize)
        returns
            self.paddr_field_spec(),
    {
        self.val & A::address_mask()
    }

    /// `paddr_field`, with the private (confidentiality) bit cleared: the
    /// frame a table walk should follow (SVSM's `page_frame`).
    pub open spec fn page_frame_spec(&self) -> usize {
        self.paddr_field_spec() & !A::spec_private_mask()
    }

    #[verifier::when_used_as_spec(page_frame_spec)]
    pub fn page_frame(&self) -> (ret: usize)
        returns
            self.page_frame_spec(),
    {
        self.paddr_field() & !A::private_pte_mask()
    }

    /// `page_frame`, with the shared bit cleared too: the *clean* physical
    /// frame, every architecture-specific tag stripped (SVSM's `address`).
    pub open spec fn address_spec(&self) -> usize {
        self.page_frame_spec() & !A::spec_shared_mask()
    }

    #[verifier::when_used_as_spec(address_spec)]
    pub fn address(&self) -> (ret: usize)
        returns
            self.address_spec(),
    {
        self.page_frame() & !A::shared_pte_mask()
    }

    /// Whether the stored address carries the architecture's shared
    /// (plaintext) tag.
    pub open spec fn is_shared_spec(&self) -> bool {
        self.paddr_field_spec() & A::spec_shared_mask() == A::spec_shared_mask()
    }

    #[verifier::when_used_as_spec(is_shared_spec)]
    pub fn is_shared(&self) -> (ret: bool)
        returns
            self.is_shared_spec(),
    {
        self.paddr_field() & A::shared_pte_mask() == A::shared_pte_mask()
    }

    /// Reads the whole word as flags. Every bit is kept, including any the
    /// architecture has no name for: the C-bit's position, for one, is a
    /// machine property rather than an architectural constant.
    pub fn flags(&self) -> (ret: A::PTFlags)
        ensures
            ret.bits_spec() == self.view(),
    {
        proof {
            A::PTFlags::lemma_flag_bits_wf();
        }
        A::PTFlags::from_bits_retain(self.val)
    }

    /// Hardware present bit.
    pub open spec fn present_spec(&self) -> bool {
        self.view() & A::PTFlags::spec_present_bit() != 0
    }

    #[verifier::when_used_as_spec(present_spec)]
    pub fn present(&self) -> (ret: bool)
        returns
            self.present_spec(),
    {
        proof {
            A::PTFlags::lemma_flag_bits_wf();
        }
        self.raw() & A::PTFlags::present_bit() != 0
    }

    /// Hardware huge (large-page) bit. At the leaf level the hardware reads
    /// this bit as PAT instead, so only a caller that knows the level may read
    /// it as "maps a large page".
    pub open spec fn huge_spec(&self) -> bool {
        self.view() & A::PTFlags::spec_huge_bit() != 0
    }

    pub fn huge(&self) -> (ret: bool)
        returns
            self.huge_spec(),
    {
        proof {
            A::PTFlags::lemma_flag_bits_wf();
        }
        self.raw() & A::PTFlags::huge_bit() != 0
    }

    /// Hardware user-accessible bit.
    pub open spec fn user_spec(&self) -> bool {
        self.view() & A::PTFlags::spec_user_bit() != 0
    }

    #[verifier::when_used_as_spec(user_spec)]
    pub fn user(&self) -> (ret: bool)
        returns
            self.user_spec(),
    {
        proof {
            A::PTFlags::lemma_flag_bits_wf();
        }
        self.raw() & A::PTFlags::user_bit() != 0
    }

    /// Whether this crate marked the entry as pointing at a table page it
    /// built, and so as escrowing that page's tokens.
    pub open spec fn escrows_spec(&self) -> bool {
        self.view() & A::PTFlags::spec_escrow_bit() != 0
    }

    #[verifier::when_used_as_spec(escrows_spec)]
    pub fn escrows(&self) -> (ret: bool)
        returns
            self.escrows_spec(),
    {
        proof {
            A::PTFlags::lemma_flag_bits_wf();
        }
        self.raw() & A::PTFlags::escrow_bit() != 0
    }

    /// An entry a walker may follow down to a child table.
    ///
    /// The hardware bits alone cannot say this. At the leaf level a present
    /// entry with the large-page bit clear maps a 4K page, and the hardware
    /// reads that bit as PAT there; above the leaf the same two bits mean
    /// "points at a table". The escrow bit is what distinguishes them at every
    /// level, and it is set only by the code in this crate that links a page it
    /// has just built.
    pub open spec fn is_table_spec(&self) -> bool {
        &&& self.present_spec()
        &&& !self.huge_spec()
        &&& self.escrows_spec()
    }

    pub fn is_table(&self) -> (ret: bool)
        returns
            self.is_table_spec(),
    {
        self.present() && !self.huge() && self.escrows()
    }

    /// A present entry that maps a page rather than pointing at a table.
    pub open spec fn is_leaf_spec(&self) -> bool {
        self.present_spec() && !self.is_table_spec()
    }

    pub fn is_leaf(&self) -> (ret: bool)
        returns
            self.is_leaf_spec(),
    {
        self.present() && !self.is_table()
    }

    /// The all-zero entry: not present, and so neither a table nor a leaf.
    pub fn empty() -> (ret: Self)
        ensures
            ret.is_clear_spec(),
            !ret.present_spec(),
    {
        let ret = Self { val: 0, dummy: PhantomData };
        assert(0usize & A::PTFlags::spec_present_bit() == 0) by (bit_vector);
        ret
    }

    /// An entry holding `addr` with `flags`. Bits of `flags` that fall inside
    /// the address field are dropped, so the address survives whatever the
    /// caller passes.
    pub fn new(addr: PhysAddr, flags: A::PTFlags) -> (ret: Self)
        requires
            addr@ & !A::spec_address_mask() == 0,
        ensures
            ret.paddr_field_spec() == addr@,
            ret.view() & !A::spec_address_mask() == flags.bits_spec() & !A::spec_address_mask(),
            ret.present_spec() == (flags.bits_spec() & A::PTFlags::spec_present_bit() != 0),
            ret.huge_spec() == (flags.bits_spec() & A::PTFlags::spec_huge_bit() != 0),
            ret.escrows_spec() == (flags.bits_spec() & A::PTFlags::spec_escrow_bit() != 0),
    {
        proof {
            A::lemma_pte_masks_wf();
            A::PTFlags::lemma_flag_bits_wf();
        }
        let masked_addr = addr.bits() & A::address_mask();
        let flag_bits = flags.bits() & !A::address_mask();
        let ret = Self { val: masked_addr | flag_bits, dummy: PhantomData };
        proof {
            let am = A::spec_address_mask();
            let pb = A::PTFlags::spec_present_bit();
            let hb = A::PTFlags::spec_huge_bit();
            let a = addr@;
            let fb = flags.bits_spec();
            let eb = A::PTFlags::spec_escrow_bit();
            assert((am & pb == 0 && am & hb == 0 && am & eb == 0 && a & !am == 0 && masked_addr == a
                & am && flag_bits == fb & !am) ==> ((masked_addr | flag_bits) & am == a && (
            masked_addr | flag_bits) & !am == fb & !am && ((masked_addr | flag_bits) & pb != 0) == (
            fb & pb != 0) && ((masked_addr | flag_bits) & hb != 0) == (fb & hb != 0) && ((
            masked_addr | flag_bits) & eb != 0) == (fb & eb != 0))) by (bit_vector);
        }
        ret
    }

    pub fn set(&mut self, addr: PhysAddr, flags: A::PTFlags)
        requires
            addr@ & !A::spec_address_mask() == 0,
        ensures
            final(self).paddr_field_spec() == addr@,
            final(self).view() & !A::spec_address_mask() == flags.bits_spec()
                & !A::spec_address_mask(),
            final(self).present_spec() == (flags.bits_spec() & A::PTFlags::spec_present_bit() != 0),
            final(self).huge_spec() == (flags.bits_spec() & A::PTFlags::spec_huge_bit() != 0),
            final(self).escrows_spec() == (flags.bits_spec() & A::PTFlags::spec_escrow_bit() != 0),
    {
        *self = Self::new(addr, flags);
    }
}

impl<A: ArchPagingMeta> Clone for PTEntry<A> {
    fn clone(&self) -> (ret: Self)
        returns
            *self,
    {
        Self { val: self.val, dummy: PhantomData }
    }
}

impl<A: ArchPagingMeta> Copy for PTEntry<A> {

}

/// A slot is read and written as a plain word; these are the two directions of
/// that, and the protocol layer keys its value type on them. The ghost side of
/// the correspondence lives in `specs::entry`.
impl<A: ArchPagingMeta> From<usize> for PTEntry<A> {
    fn from(val: usize) -> Self {
        PTEntry::from_bits(val)
    }
}

impl<A: ArchPagingMeta> From<PTEntry<A>> for usize {
    fn from(entry: PTEntry<A>) -> usize {
        entry.raw()
    }
}

/// The PIN invariant a lock-free reader depends on: once a slot is observed
/// holding a table entry, every later value of that slot is still a table
/// entry with the *same* child frame. A leaf or empty observation carries no
/// such promise -- it may already be stale by the time the reader acts on it.
pub open spec fn entry_step<A: ArchPagingMeta>(a: PTEntry<A>, b: PTEntry<A>) -> bool {
    a.is_table_spec() ==> (b.is_table_spec() && a.paddr_field_spec() == b.paddr_field_spec())
}

pub proof fn lemma_entry_step_reflexive<A: ArchPagingMeta>(a: PTEntry<A>)
    ensures
        entry_step(a, a),
{
}

pub proof fn lemma_entry_step_transitive<A: ArchPagingMeta>(
    a: PTEntry<A>,
    b: PTEntry<A>,
    c: PTEntry<A>,
)
    requires
        entry_step(a, b),
        entry_step(b, c),
    ensures
        entry_step(a, c),
{
}

} // verus!

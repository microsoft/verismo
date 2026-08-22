//! Encoding of a single hardware page-table entry: what its bits mean, and
//! the small algebra (`entry_step`) a lock-free walker relies on once a slot
//! has been observed to hold a table pointer.
//!
//! Type definitions and their specs only -- no walking, no mapping, no
//! allocation. Levels are threaded as a plain `depth` counted up from the
//! leaf (`0` is the smallest page) rather than a typed level marker, since
//! that marker is being defined elsewhere and will be plugged in later.
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
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
pub struct PageTableEntry<A: ArchPagingMeta> {
    val: usize,
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> PageTableEntry<A> {
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
    pub fn bits(&self) -> (ret: usize)
        returns
            self.view(),
    {
        self.val
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

    /// The bits outside the address field: the raw flags word, before any
    /// architecture-specific decoding.
    pub open spec fn flags_bits_spec(&self) -> usize {
        self.view() & !A::spec_address_mask()
    }

    /// Decodes the flags word into the architecture's flags type.
    pub fn flags(&self) -> (ret: A::PTFlags)
        ensures
            ret@ == self.flags_bits_spec(),
    {
        proof {
            A::lemma_pte_masks_wf();
        }
        A::PTFlags::from_bits_truncate(self.val)
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
        self.val & A::PTFlags::present_bit() != 0
    }

    /// Hardware huge (large-page) bit. A depth-0 entry maps the smallest
    /// page and is never huge, regardless of the stored bit.
    pub open spec fn huge_spec(&self, depth: nat) -> bool {
        depth > 0 && self.view() & A::PTFlags::spec_huge_bit() != 0
    }

    pub fn huge(&self, depth: usize) -> (ret: bool)
        returns
            self.huge_spec(depth as nat),
    {
        depth > 0 && self.val & A::PTFlags::huge_bit() != 0
    }

    /// A present, non-huge entry above the leaf level: the only shape a
    /// walker may follow down to a child table.
    pub open spec fn is_table_spec(&self, depth: nat) -> bool {
        self.present_spec() && !self.huge_spec(depth) && depth > 0
    }

    pub fn is_table(&self, depth: usize) -> (ret: bool)
        returns
            self.is_table_spec(depth as nat),
    {
        self.present() && !self.huge(depth) && depth > 0
    }

    /// A present entry a walk stops at: a depth-0 mapping, or a huge mapping
    /// above it.
    pub open spec fn is_leaf_spec(&self, depth: nat) -> bool {
        self.present_spec() && (depth == 0 || self.huge_spec(depth))
    }

    pub fn is_leaf(&self, depth: usize) -> (ret: bool)
        returns
            self.is_leaf_spec(depth as nat),
    {
        self.present() && (depth == 0 || self.huge(depth))
    }

    /// The all-zero entry: not present, and so neither a table nor a leaf at
    /// any depth.
    pub fn empty() -> (ret: Self)
        ensures
            ret.view() == 0,
            !ret.present_spec(),
    {
        let ret = Self { val: 0, dummy: PhantomData };
        assert(0usize & A::PTFlags::spec_present_bit() == 0) by (bit_vector);
        ret
    }

    /// A table entry pointing at `child_frame`, a page holding the next
    /// level down.
    ///
    /// `flags` must already carry `PRESENT` and clear `HUGE` -- typically
    /// `A::PTFlags::parent_flags()` plus any per-mapping bits.
    pub fn new_table(child_frame: PhysAddr, flags: A::PTFlags) -> (ret: Self)
        requires
            child_frame@ & !A::spec_address_mask() == 0,
            flags@ & A::PTFlags::spec_present_bit() != 0,
            flags@ & A::PTFlags::spec_huge_bit() == 0,
        ensures
            ret.paddr_field_spec() == child_frame@,
            forall|depth: nat| depth > 0 ==> ret.is_table_spec(depth),
    {
        proof {
            A::lemma_pte_masks_wf();
        }
        let addr = child_frame.bits() & A::address_mask();
        // Flag bits are masked out of the address field before assembly, so
        // the postconditions below hold regardless of what `flags` happens
        // to carry outside its architecture-defined bits.
        let flag_bits = flags.bits() & !A::address_mask();
        let ret = Self { val: addr | flag_bits, dummy: PhantomData };
        proof {
            let am = A::spec_address_mask();
            let pb = A::PTFlags::spec_present_bit();
            let hb = A::PTFlags::spec_huge_bit();
            let cf = child_frame@;
            let fb = flags@;
            assert(am & pb == 0 && am & hb == 0);
            assert(cf & !am == 0);
            assert(fb & pb != 0 && fb & hb == 0);
            assert(addr == cf & am);
            assert(flag_bits == fb & !am);
            assert((am & pb == 0 && am & hb == 0 && cf & !am == 0 && fb & pb != 0 && fb & hb == 0
                && addr == cf & am && flag_bits == fb & !am) ==> ((addr | flag_bits) & am == cf && (
            addr | flag_bits) & pb != 0 && (addr | flag_bits) & hb == 0)) by (bit_vector);
        }
        ret
    }

    /// A leaf entry mapping `frame` with `flags`.
    pub fn new_leaf(frame: PhysAddr, flags: A::PTFlags) -> (ret: Self)
        requires
            frame@ & !A::spec_address_mask() == 0,
            flags@ & A::PTFlags::spec_present_bit() != 0,
        ensures
            ret.paddr_field_spec() == frame@,
            ret.present_spec(),
            forall|depth: nat|
                depth > 0 ==> ret.huge_spec(depth) == (flags@ & A::PTFlags::spec_huge_bit() != 0),
            ret.is_leaf_spec(0),
    {
        proof {
            A::lemma_pte_masks_wf();
        }
        let addr = frame.bits() & A::address_mask();
        let flag_bits = flags.bits() & !A::address_mask();
        let ret = Self { val: addr | flag_bits, dummy: PhantomData };
        proof {
            let am = A::spec_address_mask();
            let pb = A::PTFlags::spec_present_bit();
            let hb = A::PTFlags::spec_huge_bit();
            let fr = frame@;
            let fb = flags@;
            assert(am & pb == 0 && am & hb == 0);
            assert(fr & !am == 0);
            assert(fb & pb != 0);
            assert(addr == fr & am);
            assert(flag_bits == fb & !am);
            assert((am & pb == 0 && am & hb == 0 && fr & !am == 0 && fb & pb != 0 && addr == fr & am
                && flag_bits == fb & !am) ==> ((addr | flag_bits) & am == fr && (addr | flag_bits)
                & pb != 0 && (addr | flag_bits) & hb == fb & hb)) by (bit_vector);
        }
        ret
    }
}

impl<A: ArchPagingMeta> Clone for PageTableEntry<A> {
    fn clone(&self) -> (ret: Self)
        returns
            *self,
    {
        Self { val: self.val, dummy: PhantomData }
    }
}

impl<A: ArchPagingMeta> Copy for PageTableEntry<A> {

}

/// The PIN invariant a lock-free reader depends on: once a slot is observed
/// holding a table entry, every later value of that slot is still a table
/// entry with the *same* child frame. A leaf or empty observation carries no
/// such promise -- it may already be stale by the time the reader acts on it.
/// A slot is read and written as a plain word; these are the two directions of
/// that, and the protocol layer keys its value type on them. The ghost side of
/// the correspondence lives in `specs::entry`.
impl<A: ArchPagingMeta> From<usize> for PageTableEntry<A> {
    fn from(val: usize) -> Self {
        PageTableEntry::from_bits(val)
    }
}

impl<A: ArchPagingMeta> From<PageTableEntry<A>> for usize {
    fn from(entry: PageTableEntry<A>) -> usize {
        entry.bits()
    }
}


pub open spec fn entry_step<A: ArchPagingMeta>(
    a: PageTableEntry<A>,
    b: PageTableEntry<A>,
    depth: nat,
) -> bool {
    a.is_table_spec(depth) ==> (b.is_table_spec(depth) && a.paddr_field_spec()
        == b.paddr_field_spec())
}

pub proof fn lemma_entry_step_reflexive<A: ArchPagingMeta>(a: PageTableEntry<A>, depth: nat)
    ensures
        entry_step(a, a, depth),
{
}

pub proof fn lemma_entry_step_transitive<A: ArchPagingMeta>(
    a: PageTableEntry<A>,
    b: PageTableEntry<A>,
    c: PageTableEntry<A>,
    depth: nat,
)
    requires
        entry_step(a, b, depth),
        entry_step(b, c, depth),
    ensures
        entry_step(a, c, depth),
{
}

} // verus!

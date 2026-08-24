//! x86_64 four-level paging, as the crate's contracts describe it.
//!
//! This is the first concrete instance of `ArchPagingMeta`, and its real job is
//! to show that the obligations the contracts impose can be discharged: the
//! geometry, the mask relations, and the flag bit positions are all proved here
//! for the architecture, once, so no caller carries them.
//!
//! The confidentiality bit is a *parameter*, not a constant: on SEV-SNP the
//! firmware reports which bit of the physical address encrypts a page, so the
//! type is generic over a marker that supplies it.
use vstd::prelude::*;

use crate::structs::address::PhysAddr;
use crate::structs::arch_contract::{
    level_geometry_wf, ArchPagingGeometry, ArchPagingMeta, GenericPageTableFlagsSpec,
};
use crate::structs::entry::PTEntry;
use crate::structs::ptpage::PTPage;
use crate::structs::level::PageLevel;
use crate::structs::sizes::{lemma_size_4k, PageOffset, Size4KiB};
use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power2::pow2;

use super::pt_flags::PTEntryFlags;

verus! {

/// Where the platform has mapped physical memory, and which address bit
/// encrypts a page.
///
/// Both are runtime facts on a confidential-computing host -- the C-bit is
/// reported by CPUID, and the direct map is where the loader put it -- so they
/// are supplied by the embedder rather than fixed here.
pub trait X86PagingParams: 'static {
    /// The single address bit that marks a page private, or zero if memory is
    /// not encrypted.
    spec fn spec_private_mask() -> usize;

    /// Where the physical frame `paddr` is readable.
    spec fn spec_paddr_to_vaddr(paddr: usize) -> usize;

    fn private_mask() -> (ret: usize)
        ensures
            ret == Self::spec_private_mask(),
    ;

    /// The C-bit lies inside the 52-bit physical address field, which is what
    /// lets a tagged address still be stored in an entry.
    proof fn lemma_private_mask_wf()
        ensures
            Self::spec_private_mask() & !0x000f_ffff_ffff_f000usize == 0,
    ;
}

/// x86_64 paging with 4 KiB pages and 512-entry tables.
pub struct X86Paging<P: X86PagingParams> {
    dummy: core::marker::PhantomData<P>,
}

impl<P: X86PagingParams> Clone for X86Paging<P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P: X86PagingParams> Copy for X86Paging<P> {

}

impl<P: X86PagingParams> ArchPagingGeometry for X86Paging<P> {
    type MinPageSize = Size4KiB;

    /// 52 bits, the widest the architecture defines.
    open spec fn phys_addr_width() -> nat {
        52
    }

    open spec fn spec_paddr_to_vaddr(paddr: usize) -> usize {
        P::spec_paddr_to_vaddr(paddr)
    }

    open spec fn spec_entries_per_page() -> nat {
        512
    }

    open spec fn spec_index_width() -> nat {
        9
    }

    proof fn lemma_geometry_wf() {
        lemma_size_4k();
    }
}

impl<P: X86PagingParams> ArchPagingMeta for X86Paging<P> {
    type PTFlags = PTEntryFlags;

    fn entries_per_page() -> (ret: usize) {
        512
    }

    fn index_width() -> (ret: usize) {
        9
    }

    open spec fn spec_private_mask() -> usize {
        P::spec_private_mask()
    }

    /// Nothing is shared unless the embedder says so; the shared bit is the
    /// absence of the private one on SEV-SNP.
    open spec fn spec_shared_mask() -> usize {
        0
    }

    open spec fn spec_address_mask() -> usize {
        0x000f_ffff_ffff_f000
    }

    proof fn lemma_pte_masks_wf() {
        PTEntryFlags::lemma_flag_bits_wf();
        P::lemma_private_mask_wf();
        assert(0x000f_ffff_ffff_f000usize & 0x1usize == 0) by (bit_vector);
        assert(0x000f_ffff_ffff_f000usize & 0x80usize == 0) by (bit_vector);
        assert(0x000f_ffff_ffff_f000usize & 0x200usize == 0) by (bit_vector);
        assert(0x8000_0000_0000_03ffusize & !0x000f_ffff_ffff_f000usize
            == 0x8000_0000_0000_03ffusize) by (bit_vector);
        assert(forall|m: usize| m & 0usize == 0) by (bit_vector);
        assert(0usize & !0x000f_ffff_ffff_f000usize == 0) by (bit_vector);
    }

    fn private_pte_mask() -> (ret: usize) {
        P::private_mask()
    }

    fn shared_pte_mask() -> (ret: usize) {
        0
    }

    fn address_mask() -> (ret: usize) {
        0x000f_ffff_ffff_f000
    }

    fn supported_flags() -> Self::PTFlags {
        PTEntryFlags::all()
    }
}

/// The geometry predicate the rest of the crate carries as a precondition,
/// discharged once for x86_64: 512 eight-byte entries to a 4 KiB page, nine
/// address bits to a level, and a four-level tree that spans 48 bits.
pub proof fn lemma_x86_geometry_wf<P: X86PagingParams>()
    ensures
        level_geometry_wf::<X86Paging<P>>(),
{
    lemma_size_4k();
    assert(PTPage::<X86Paging<P>>::count() == 512);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2(9);
    vstd::arithmetic::logarithm::lemma_log_pow(2, 9);
    PageLevel::lemma_depth_roundtrip(PageLevel::Level4);
}

} // verus!

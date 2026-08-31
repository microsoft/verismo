// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
use crate::arch::x86_64::paging::{X86Paging, X86PagingParams};
use crate::specs::external::SpecVAddrImpl;
use crate::specs::external::{exists_into, forall_into};
use crate::structs::arch_contract::ArchPagingGeometry;
use crate::structs::entry::{lemma_pgtbl_idx_step, lemma_pgtbl_idx_zero, pgtbl_idx};
use crate::structs::level::PageLevel;
use crate::structs::ptpage::PTPage;
use crate::structs::sizes::{MinPageSize, PAGE_SIZE};
use crate::util::{align_down_integer_ens, align_up_integer_ens, proof_align_down, proof_align_up};
use vstd::arithmetic::div_mod::lemma_div_by_multiple;
use vstd::raw_ptr::{ptr_from_data, ptr_mut_from_data, PtrData};
use vstd::set_lib::set_int_range;
use vstd::std_specs::cmp::PartialOrdSpec;
use vstd::std_specs::convert::{FromSpec, IntoSpec};
use vstd::std_specs::ops::AddSpec;

verus! {

pub broadcast group sign_extend_proof {
    common_proofs::bits::lemma_bit_usize_not_is_sub,
    common_proofs::bits::lemma_bit_usize_shl_values,
    common_proofs::bits::lemma_bit_usize_or_mask,
    common_proofs::bits::lemma_bit_usize_and_mask,
    lemma_check_sign_bit,
}

pub broadcast group address_align_proof {
    crate::sizes::group_types_proof,
    common_proofs::bits::lemma_bit_usize_and_mask_is_mod,
    proof_align_up,
    proof_align_down,
    address_spec::lemma_align_up_requires,
    address_spec::lemma_align_up_ens,
}

broadcast group vaddr_impl_proof {
    sign_extend_proof,
    address_spec::lemma_inner_addr_as_vaddr,
    address_spec::lemma_upper_address_has_sign_bit,
    common_proofs::bits::lemma_bit_usize_and_mask_is_mod,
    address_align_proof,
    address_spec::reveal_pfn,
}

pub broadcast group group_addr_proofs {
    VirtAddr::property_canonical,
    VirtAddr::lemma_wf,
}

broadcast use vaddr_impl_proof;

/// Define a broadcast function and its related spec function calls in a inner
/// module to avoid cyclic self-reference
#[path = "address_inner.rs"]
mod address_spec;

pub use address_spec::*;

// The inner address should be smaller than VADDR_RANGE_SIZE.
// Define a simple spec for sign_extend without using bit ops.
pub open spec fn sign_extend_spec(addr: InnerAddr) -> usize
    recommends
        addr < VADDR_RANGE_SIZE,
{
    if addr <= VADDR_LOWER_MASK {
        addr
    } else if addr < VADDR_RANGE_SIZE {
        (addr - VADDR_LOWER_MASK - 1 + VADDR_UPPER_MASK) as usize
    } else {
        sign_extend_impl(addr)
    }
}

// closed since external function should assume addr < VADDR_RANGE_SIZE.
pub closed spec fn sign_extend_impl(addr: InnerAddr) -> InnerAddr {
    if check_sign_bit(addr) {
        (vaddr_lower_bits(addr) + VADDR_UPPER_MASK) as InnerAddr
    } else {
        vaddr_lower_bits(addr)
    }
}

/// Sign extension is the identity on an address that is already canonical.
/// This is what lets a caller move a virtual address within its own half --
/// aligning it down to a page start, say -- and rebuild a `VirtAddr` from the
/// result without the address moving again.
pub proof fn lemma_sign_extend_canonical(v: InnerAddr)
    requires
        v <= VADDR_LOWER_MASK || v >= VADDR_UPPER_MASK,
    ensures
        sign_extend_spec(v) == v,
{
    if v > VADDR_LOWER_MASK {
        assert(VADDR_UPPER_MASK >= VADDR_RANGE_SIZE);
        assert(vaddr_upper_bits(v) == VADDR_UPPER_MASK);
    }
}

/// Ensures that ret is a new canonical address, throwing out bits 48..64.
#[verifier(inline)]
pub open spec fn sign_extend_ensures(addr: InnerAddr, ret: InnerAddr) -> bool {
    &&& ret == sign_extend_spec(addr)
    &&& vaddr_lower_bits(ret) == vaddr_lower_bits(addr)
}

pub open spec fn pt_idx_spec(addr: InnerAddr, l: usize) -> usize
    recommends
        l <= 5,
{
    let upper = match l {
        0usize => { addr >> 12 },
        1usize => { addr >> 21 },
        2usize => { addr >> 30 },
        3usize => { addr >> 39 },
        4usize => { addr >> 48 },
        5usize => { addr >> 57 },
        _ => { 0 },
    };
    upper % 512
}

pub proof fn lemma_pt_idx_spec_is_pgtbl_idx_x86<P: X86PagingParams>(addr: InnerAddr, l: usize)
    requires
        l <= 4,
    ensures
        pt_idx_spec(addr, l) == pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(l as nat)),
{
    lemma_size_4k();
    assert(PAGE_SIZE == 4096usize);
    assert(PTPage::<X86Paging<P>>::count() == 512);
    let page_size = 4096usize;
    let entry_count = 512usize;
    let vp0 = addr / page_size;
    let vp1 = vp0 / entry_count;
    let vp2 = vp1 / entry_count;
    let vp3 = vp2 / entry_count;
    let vp4 = vp3 / entry_count;
    lemma_div_by_multiple(vp1 as int, page_size as int);
    lemma_div_by_multiple(vp2 as int, page_size as int);
    lemma_div_by_multiple(vp3 as int, page_size as int);
    lemma_div_by_multiple(vp4 as int, page_size as int);
    assert((vp1 as nat * 4096nat) / 4096nat == vp1 as nat);
    assert((vp2 as nat * 4096nat) / 4096nat == vp2 as nat);
    assert((vp3 as nat * 4096nat) / 4096nat == vp3 as nat);
    assert((vp4 as nat * 4096nat) / 4096nat == vp4 as nat);
    assert(addr as nat / 4096nat == vp0 as nat);
    assert((vp0 as nat) / 512nat == vp1 as nat);
    assert((vp1 as nat) / 512nat == vp2 as nat);
    assert((vp2 as nat) / 512nat == vp3 as nat);
    assert((vp3 as nat) / 512nat == vp4 as nat);
    vstd::arithmetic::div_mod::lemma_div_denominator(
        addr as int,
        page_size as int,
        entry_count as int,
    );
    vstd::arithmetic::div_mod::lemma_div_denominator(
        addr as int,
        (page_size * entry_count) as int,
        entry_count as int,
    );
    vstd::arithmetic::div_mod::lemma_div_denominator(
        addr as int,
        (page_size * entry_count * entry_count) as int,
        entry_count as int,
    );
    vstd::arithmetic::div_mod::lemma_div_denominator(
        addr as int,
        (page_size * entry_count * entry_count * entry_count) as int,
        entry_count as int,
    );
    assert((addr >> 12usize) == addr / 4096usize) by (bit_vector);
    assert((addr >> 21usize) == addr / 2097152usize) by (bit_vector);
    assert((addr >> 30usize) == addr / 1073741824usize) by (bit_vector);
    assert((addr >> 39usize) == addr / 549755813888usize) by (bit_vector);
    assert((addr >> 48usize) == addr / 281474976710656usize) by (bit_vector);
    assert(4096usize * 512usize == 2097152usize) by (compute);
    assert(4096usize * 512usize * 512usize == 1073741824usize) by (compute);
    assert(4096usize * 512usize * 512usize * 512usize == 549755813888usize) by (compute);
    assert(4096usize * 512usize * 512usize * 512usize * 512usize == 281474976710656usize)
        by (compute);
    assert(page_size * entry_count == 2097152);
    assert(page_size * entry_count * entry_count == 1073741824);
    assert(page_size * entry_count * entry_count * entry_count == 549755813888);
    assert(page_size * entry_count * entry_count * entry_count * entry_count == 281474976710656);
    assert((vp0 % entry_count) as nat == (vp0 as nat) % 512nat);
    assert((vp1 % entry_count) as nat == (vp1 as nat) % 512nat);
    assert((vp2 % entry_count) as nat == (vp2 as nat) % 512nat);
    assert((vp3 % entry_count) as nat == (vp3 as nat) % 512nat);
    assert((vp4 % entry_count) as nat == (vp4 as nat) % 512nat);
    lemma_pgtbl_idx_zero::<X86Paging<P>>(addr);
    assert(pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(0nat)) == vp0 % entry_count);
    lemma_pgtbl_idx_step::<X86Paging<P>>(addr, PageLevel::from_nat(1nat));
    lemma_pgtbl_idx_zero::<X86Paging<P>>((vp1 as nat * 4096nat) as usize);
    assert((pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(1nat)) as nat) == (vp1 as nat)
        % 512nat);
    assert(pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(1nat)) == vp1 % entry_count);
    lemma_pgtbl_idx_step::<X86Paging<P>>(addr, PageLevel::from_nat(2nat));
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp1 as nat * 4096nat) as usize,
        PageLevel::from_nat(1nat),
    );
    lemma_pgtbl_idx_zero::<X86Paging<P>>((vp2 as nat * 4096nat) as usize);
    assert((pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(2nat)) as nat) == (vp2 as nat)
        % 512nat);
    assert(pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(2nat)) == vp2 % entry_count);
    lemma_pgtbl_idx_step::<X86Paging<P>>(addr, PageLevel::from_nat(3nat));
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp1 as nat * 4096nat) as usize,
        PageLevel::from_nat(2nat),
    );
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp2 as nat * 4096nat) as usize,
        PageLevel::from_nat(1nat),
    );
    lemma_pgtbl_idx_zero::<X86Paging<P>>((vp3 as nat * 4096nat) as usize);
    assert(pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(3nat)) == vp3 % entry_count);
    lemma_pgtbl_idx_step::<X86Paging<P>>(addr, PageLevel::from_nat(4nat));
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp1 as nat * 4096nat) as usize,
        PageLevel::from_nat(3nat),
    );
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp2 as nat * 4096nat) as usize,
        PageLevel::from_nat(2nat),
    );
    lemma_pgtbl_idx_step::<X86Paging<P>>(
        (vp3 as nat * 4096nat) as usize,
        PageLevel::from_nat(1nat),
    );
    lemma_pgtbl_idx_zero::<X86Paging<P>>((vp4 as nat * 4096nat) as usize);
    assert(pgtbl_idx::<X86Paging<P>>(addr, PageLevel::from_nat(4nat)) == vp4 % entry_count);
    if l == 0 {
        assert(pt_idx_spec(addr, l) == vp0 % entry_count);
    } else if l == 1 {
        assert(pt_idx_spec(addr, l) == vp1 % entry_count);
    } else if l == 2 {
        assert(pt_idx_spec(addr, l) == vp2 % entry_count);
    } else if l == 3 {
        assert(pt_idx_spec(addr, l) == vp3 % entry_count);
    } else {
        assert(l == 4);
        assert(pt_idx_spec(addr, l) == vp4 % entry_count);
    }
}

pub open spec fn crosses_page_ens<T: Into<InnerAddr>>(addr: T, size: InnerAddr, ret: bool) -> bool {
    exists_into(addr, |inner| ret == (pfn_spec(inner) != pfn_spec((inner + size - 1) as InnerAddr)))
}

// Define a view (@) for VirtAddr
impl View for VirtAddr {
    type V = InnerAddr;

    closed spec fn view(&self) -> InnerAddr {
        self.0
    }
}

impl VirtAddr {
    /// Canonical form addresses run from 0 through 00007FFF'FFFFFFFF,
    /// and from FFFF8000'00000000 through FFFFFFFF'FFFFFFFF.
    #[verifier::type_invariant]
    pub open spec fn is_canonical(&self) -> bool {
        self.is_low() || self.is_high()
    }

    /// Property:
    /// A valid virtual address have a canonical form where the upper bits
    /// are either all zeroes or all ones.
    pub broadcast proof fn property_canonical(&self)
        ensures
            #[trigger] self.is_canonical() == (top_all_zeros(self@) || top_all_ones(self@)),
            self.is_canonical() == (*self === VirtAddr::from_spec(self.offset() as usize)),
            self.is_canonical() ==> self.offset() == if self.is_low() {
                self@ as int
            } else {
                self@ - 0xffff_0000_0000_0000
            },
    {
        broadcast use common_proofs::bits::lemma_bit_usize_not_is_sub;

        assert(VADDR_UPPER_MASK == 0xffff_8000_0000_0000);
    }

    pub broadcast proof fn lemma_wf(v: InnerAddr)
        ensures
            (#[trigger] VirtAddr::from_spec(v)).is_canonical(),
            0 <= v < VADDR_RANGE_SIZE ==> VirtAddr::from_spec(v).offset() == v,
    {
    }

    pub open spec fn is_low(&self) -> bool {
        self@ <= VADDR_LOWER_MASK
    }

    pub open spec fn is_high(&self) -> bool {
        self@ >= VADDR_UPPER_MASK
    }

    // Virtual memory offset indicating the distance from 0
    pub open spec fn offset(&self) -> int
        recommends
            self.is_canonical(),
    {
        if self.is_low() {
            self@ as int
        } else if self.is_high() {
            self@ - VADDR_UPPER_MASK + VADDR_LOWER_MASK + 1
        } else {
            -1
        }
    }

    pub open spec fn new_ensures(self, addr: InnerAddr) -> bool {
        sign_extend_ensures(addr, self@)
    }

    pub open spec fn pgtbl_idx_ensures(&self, l: usize, ret: usize) -> bool {
        ret == pt_idx_spec(self@, l)
    }

    pub open spec fn pfn_spec(&self) -> InnerAddr {
        pfn_spec(self@)
    }
}

impl VirtAddr {
    pub open spec fn spec_add_ensures(self, offset: InnerAddr, ret: VirtAddr) -> bool {
        &&& self.offset() + offset == ret.offset()
        &&& ret === VirtAddr::from_spec((self@ + offset) as InnerAddr)
        &&& ret === VirtAddr::from_spec((self.offset() + offset) as InnerAddr)
    }
}

impl vstd::std_specs::ops::AddSpecImpl<InnerAddr> for VirtAddr {
    /// Do not assume they are both high/low addresses.
    open spec fn add_req(self, offset: InnerAddr) -> bool {
        self.offset() + offset < VADDR_RANGE_SIZE
    }

    open spec fn add_spec(self, offset: InnerAddr) -> VirtAddr {
        VirtAddr::from_spec((self@ + offset) as InnerAddr)
    }

    open spec fn obeys_add_spec() -> bool {
        true
    }
}

// Get a new addr by subtracting an offset from an existing virtual address
impl vstd::std_specs::ops::SubSpecImpl<InnerAddr> for VirtAddr {
    open spec fn sub_req(self, offset: InnerAddr) -> bool {
        self.offset() >= offset
    }

    open spec fn obeys_sub_spec() -> bool {
        true
    }

    open spec fn sub_spec(self, offset: InnerAddr) -> VirtAddr {
        VirtAddr::from_spec((self@ - offset) as InnerAddr)
    }
}

// Compute the offset between two virtual addresses.
impl vstd::std_specs::ops::SubSpecImpl<VirtAddr> for VirtAddr {
    /// Do not assume they are both high/low addresses.
    open spec fn sub_req(self, rhs: VirtAddr) -> bool {
        self@ >= rhs@
    }

    open spec fn obeys_sub_spec() -> bool {
        true
    }

    open spec fn sub_spec(self, rhs: VirtAddr) -> InnerAddr {
        (self.offset() - rhs.offset()) as _
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*mut T> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(v: *mut T) -> Self {
        VirtAddr(sign_extend_spec(v as InnerAddr))
    }
}

impl<T> vstd::std_specs::convert::FromSpecImpl<*const T> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(v: *const T) -> Self {
        VirtAddr(sign_extend_spec(v as InnerAddr))
    }
}

impl vstd::std_specs::convert::FromSpecImpl<InnerAddr> for VirtAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(v: InnerAddr) -> Self {
        VirtAddr(sign_extend_spec(v))
    }
}

impl vstd::std_specs::convert::FromSpecImpl<VirtAddr> for InnerAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: VirtAddr) -> Self {
        v@
    }
}

impl vstd::std_specs::convert::FromSpecImpl<VirtAddr> for u64 {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: VirtAddr) -> Self {
        v@ as u64
    }
}

/// @Property: address can be identified by an integer.
impl SpecVAddrImpl for VirtAddr {
    #[verifier(inline)]
    open spec fn spec_int_addr(&self) -> Option<int> {
        Some(self@ as int)
    }

    #[verifier(opaque)]
    open spec fn region_to_dom(&self, size: nat) -> Set<int> {
        if self.is_canonical() {
            Set::<int>::range(0, usize::MAX + 1).filter(
                |v: int|
                    exists|addr: VirtAddr|
                        addr@ == v && addr.is_canonical() && self.offset() <= addr.offset()
                            < self.offset() + size,
            )
        } else {
            Set::empty()
        }
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_unique(v1: &Self, v2: &Self) {
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_vaddr_region_len(&self, size: nat)
        ensures
            self.is_canonical() ==> self.region_to_dom(size).len() > 0,
    {
        reveal(<VirtAddr as SpecVAddrImpl>::region_to_dom);
        if self.is_canonical() {
            assert(self.region_to_dom(size).contains(self@ as int));
        }
        self.lemma_valid_small_size(1, size);
        vstd::set_lib::lemma_int_range(0, usize::MAX + 1);
        vstd::set_lib::lemma_len_subset(self.region_to_dom(1), set_int_range(0, usize::MAX + 1));
        vstd::set_lib::lemma_len_subset(self.region_to_dom(size), set_int_range(0, usize::MAX + 1));
        vstd::set_lib::lemma_len_subset(self.region_to_dom(1), self.region_to_dom(size));
    }

    #[verifier(spinoff_prover)]
    proof fn lemma_valid_small_size(&self, size1: nat, size2: nat) {
        reveal(<VirtAddr as SpecVAddrImpl>::region_to_dom);
    }
}

impl VirtAddr {
    #[verifier(spinoff_prover)]
    pub proof fn lemma_region_to_dom_merge(self, size1: nat, vaddr2: VirtAddr, size2: nat)
        requires
            self.is_canonical() && vaddr2.is_canonical(),
            vaddr2.offset() == self.offset() + size1,
        ensures
            self.region_to_dom(size1) + vaddr2.region_to_dom(size2) == self.region_to_dom(
                size1 + size2,
            ),
            self.region_to_dom(size1 + size2).difference(self.region_to_dom(size1))
                == vaddr2.region_to_dom(size2),
    {
        reveal(<VirtAddr as SpecVAddrImpl>::region_to_dom);
        assert(self.region_to_dom(size1) + vaddr2.region_to_dom(size2) =~= self.region_to_dom(
            size1 + size2,
        ));
        assert(self.region_to_dom(size1 + size2).difference(self.region_to_dom(size1))
            =~= vaddr2.region_to_dom(size2))
    }
}

// Define a view (@) for PhysAddr
impl View for PhysAddr {
    type V = InnerAddr;

    closed spec fn view(&self) -> InnerAddr {
        self.0
    }
}

impl vstd::std_specs::convert::FromSpecImpl<InnerAddr> for PhysAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    closed spec fn from_spec(v: InnerAddr) -> Self {
        PhysAddr(v)
    }
}

/// A physical address is its inner word. Both directions of that are `closed`,
/// so a caller outside this module needs it stated.
pub proof fn lemma_phys_addr_from_bits(v: InnerAddr)
    ensures
        <PhysAddr as vstd::std_specs::convert::FromSpec<InnerAddr>>::from_spec(v)@ == v,
{
}

impl vstd::std_specs::convert::FromSpecImpl<PhysAddr> for InnerAddr {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: PhysAddr) -> Self {
        v@
    }
}

impl vstd::std_specs::convert::FromSpecImpl<PhysAddr> for u64 {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: PhysAddr) -> Self {
        v@ as u64
    }
}

impl vstd::std_specs::ops::SubSpecImpl<PhysAddr> for PhysAddr {
    /// Do not assume they are both high/low addresses.
    open spec fn sub_req(self, rhs: PhysAddr) -> bool {
        self@ >= rhs@
    }

    open spec fn obeys_sub_spec() -> bool {
        true
    }

    open spec fn sub_spec(self, rhs: PhysAddr) -> InnerAddr {
        (self@ - rhs@) as _
    }
}

impl vstd::std_specs::ops::SubSpecImpl<InnerAddr> for PhysAddr {
    /// Do not assume they are both high/low addresses.
    open spec fn sub_req(self, rhs: InnerAddr) -> bool {
        self@ >= rhs
    }

    open spec fn obeys_sub_spec() -> bool {
        true
    }

    open spec fn sub_spec(self, rhs: InnerAddr) -> PhysAddr {
        PhysAddr::from_spec((self@ - rhs) as InnerAddr)
    }
}

impl vstd::std_specs::ops::AddSpecImpl<InnerAddr> for PhysAddr {
    /// Do not assume they are both high/low addresses.
    open spec fn add_req(self, offset: InnerAddr) -> bool {
        self@ + offset <= InnerAddr::MAX
    }

    open spec fn obeys_add_spec() -> bool {
        true
    }

    open spec fn add_spec(self, offset: InnerAddr) -> PhysAddr {
        PhysAddr::from_spec((self@ + offset) as InnerAddr)
    }
}

/// Assumptions for PartialOrd since it is derived.
impl vstd::std_specs::cmp::PartialOrdSpecImpl<VirtAddr> for VirtAddr {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &VirtAddr) -> Option<core::cmp::Ordering> {
        PartialOrdSpec::partial_cmp_spec(&self@, &other@)
    }
}

/// Assumptions for PartialOrd since it is derived.
impl vstd::std_specs::cmp::PartialOrdSpecImpl<PhysAddr> for PhysAddr {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &PhysAddr) -> Option<core::cmp::Ordering> {
        PartialOrdSpec::partial_cmp_spec(&self@, &other@)
    }
}

/// Assumptions for PartialEq since it is derived.
pub assume_specification[ <VirtAddr as PartialEq<VirtAddr>>::eq ](
    x: &VirtAddr,
    y: &VirtAddr,
) -> bool
;

/// Assumptions for PartialEq since it is derived.
impl vstd::std_specs::cmp::PartialEqSpecImpl<VirtAddr> for VirtAddr {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &VirtAddr) -> bool {
        self@ == other@
    }
}

/// Assumptions for PartialEq since it is derived.
pub assume_specification[ <PhysAddr as PartialEq<PhysAddr>>::eq ](
    x: &PhysAddr,
    y: &PhysAddr,
) -> bool
;

/// Assumptions for PartialEq since it is derived.
impl vstd::std_specs::cmp::PartialEqSpecImpl<PhysAddr> for PhysAddr {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &PhysAddr) -> bool {
        self@ == other@
    }
}

} // verus!

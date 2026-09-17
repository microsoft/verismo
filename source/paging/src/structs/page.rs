// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
//! Virtual memory pages, following the `x86_64` crate's
//! `structures::paging::page`.
//!
//! A [`Page`] is the virtual counterpart of [`crate::frame::PhysFrame`]: a
//! virtual address carrying a proof that it starts a page of the size it is
//! typed with. The two are deliberately separate types, so a mapping is a
//! relation between values that cannot be confused for one another.
//!
//! As in `frame`, the iterator impls of the original are absent.
use core::marker::PhantomData;

use builtin_macros::*;
use vstd::prelude::*;

use crate::structs::address::{Address, VirtAddr};
#[cfg(verus_only)]
use crate::structs::address::VADDR_UPPER_MASK;
use crate::structs::sizes::{PageSize, Size4KiB};

#[cfg(verus_only)]
include!("../specs/page.rs");

/// An address that is not the start of a page.
#[verus_verify(external_derive)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddressNotAligned;

/// A virtual memory page of size `S`.
#[verus_verify]
#[repr(C)]
pub struct Page<S: PageSize = Size4KiB> {
    start_address: VirtAddr,
    size: PhantomData<S>,
}

#[verus_verify]
impl<S: PageSize> Page<S> {
    /// The page starting at `address`, or an error if that address is not the
    /// start of a page.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.is_ok() == is_aligned_spec(address@, S::SIZE),
            ret.is_ok() ==> ret.unwrap()@ == address@,
    )]
    pub fn from_start_address(address: VirtAddr) -> Result<Self, AddressNotAligned> {
        if !address.is_page_aligned::<S>() {
            return Err(AddressNotAligned);
        }
        proof! { S::lemma_size_wf(); }
        Ok(Page { start_address: address, size: PhantomData })
    }

    /// The page starting at `start_address`.
    ///
    /// Safe, unlike the original: the alignment the `unsafe` version asks the
    /// caller to guarantee is a precondition here, so it is checked.
    #[inline]
    #[verus_spec(ret =>
        requires
            is_aligned_spec(start_address@, S::SIZE),
        ensures
            ret@ == start_address@,
    )]
    pub fn from_start_address_unchecked(start_address: VirtAddr) -> Self {
        proof! { S::lemma_size_wf(); }
        Page { start_address, size: PhantomData }
    }

    /// The page containing `address`.
    ///
    /// A virtual address is canonical, not arbitrary, so aligning one down has
    /// to stay inside the half it came from. That holds exactly when the page
    /// size divides the canonical boundary, which is the precondition; every
    /// architectural page size (4 KiB, 2 MiB, 1 GiB) satisfies it, but nothing
    /// in `PageSize` bounds `SIZE` below the boundary, so it must be said.
    #[inline]
    #[verus_spec(ret =>
        requires
            is_aligned_spec(VADDR_UPPER_MASK, S::SIZE),
        ensures
            ret@ == address@ - address@ % S::SIZE,
    )]
    pub fn containing_address(address: VirtAddr) -> Self {
        proof! {
            use_type_invariant(&address);
            broadcast use group_addr_proofs;

            S::lemma_size_wf();
        }
        let bits = address.bits();
        proof! { lemma_mod_decreases(bits as nat, S::SIZE as nat); }
        let start = VirtAddr::new(bits - bits % S::SIZE);
        proof! {
            lemma_align_down_is_aligned(bits as int, S::SIZE as int);
            if bits >= VADDR_UPPER_MASK {
                lemma_align_down_stays_above(bits as int, VADDR_UPPER_MASK as int, S::SIZE as int);
            }
            lemma_sign_extend_canonical((bits - bits % S::SIZE) as usize);
        }
        Page { start_address: start, size: PhantomData }
    }

    /// The address this page starts at.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret@ == self@,
    )]
    pub fn start_address(self) -> VirtAddr {
        self.start_address
    }

    /// The size of this page in bytes.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == S::SIZE,
    )]
    pub fn size(self) -> usize {
        S::SIZE
    }

    /// This page's number: its start address divided by the page size.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_page_number(),
    )]
    pub fn page_number(self) -> usize {
        proof! { S::lemma_size_wf(); }
        self.start_address.bits() / S::SIZE
    }

    /// The index this page takes in the page table at level `L`.
    #[inline]
    #[verus_spec(ret =>
        requires
            L <= 5,
        ensures
            ret == pt_idx_spec(self@, L),
    )]
    pub fn table_index<const L: usize>(self) -> usize {
        self.start_address.to_pgtbl_idx::<L>()
    }

    /// The pages from `start` up to, but not including, `end`.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.start == start,
            ret.end == end,
    )]
    pub fn range(start: Page<S>, end: Page<S>) -> PageRange<S> {
        PageRange { start, end }
    }

    /// The pages from `start` up to and including `end`.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.start == start,
            ret.end == end,
    )]
    pub fn range_inclusive(start: Page<S>, end: Page<S>) -> PageRangeInclusive<S> {
        PageRangeInclusive { start, end }
    }
}

/// A range of virtual pages, `end` exclusive.
#[verus_verify]
#[repr(C)]
pub struct PageRange<S: PageSize = Size4KiB> {
    /// The first page of the range.
    pub start: Page<S>,
    /// The page after the last one of the range.
    pub end: Page<S>,
}

#[verus_verify]
impl<S: PageSize> PageRange<S> {
    /// Whether the range holds no pages.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == (self.start@ >= self.end@),
    )]
    pub fn is_empty(&self) -> bool {
        self.start.start_address().bits() >= self.end.start_address().bits()
    }

    /// The number of pages in the range.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_len(),
    )]
    pub fn len(&self) -> usize {
        if !self.is_empty() {
            proof! { lemma_page_number_ordered(self.start, self.end); }
            self.end.page_number() - self.start.page_number()
        } else {
            0
        }
    }

    /// The number of bytes the range covers.
    #[inline]
    #[verus_spec(ret =>
        requires
            self.spec_len() * S::SIZE <= usize::MAX,
        ensures
            ret == self.spec_len() * S::SIZE,
    )]
    pub fn size(&self) -> usize {
        self.len() * S::SIZE
    }
}

/// A range of virtual pages, `end` inclusive.
#[verus_verify]
#[repr(C)]
pub struct PageRangeInclusive<S: PageSize = Size4KiB> {
    /// The first page of the range.
    pub start: Page<S>,
    /// The last page of the range.
    pub end: Page<S>,
}

#[verus_verify]
impl<S: PageSize> PageRangeInclusive<S> {
    /// Whether the range holds no pages.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == (self.start@ > self.end@),
    )]
    pub fn is_empty(&self) -> bool {
        self.start.start_address().bits() > self.end.start_address().bits()
    }

    /// The number of pages in the range.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_len(),
    )]
    pub fn len(&self) -> usize {
        if !self.is_empty() {
            proof! {
                lemma_page_number_ordered(self.start, self.end);
                lemma_page_number_lt_max(self.end);
            }
            self.end.page_number() - self.start.page_number() + 1
        } else {
            0
        }
    }

    /// The number of bytes the range covers.
    #[inline]
    #[verus_spec(ret =>
        requires
            self.spec_len() * S::SIZE <= usize::MAX,
        ensures
            ret == self.spec_len() * S::SIZE,
    )]
    pub fn size(&self) -> usize {
        self.len() * S::SIZE
    }
}

// See the note in `frame`: `derive(Copy)` would demand `S: Copy`.
impl<S: PageSize> Clone for Page<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for Page<S> {}

impl<S: PageSize> Clone for PageRange<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for PageRange<S> {}

impl<S: PageSize> Clone for PageRangeInclusive<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for PageRangeInclusive<S> {}

// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
//! Physical memory frames, following the `x86_64` crate's
//! `structures::paging::frame`.
//!
//! A [`PhysFrame`] is a physical address carrying a proof that it is aligned to
//! the page size it is typed with. That is the whole content of the type, and
//! it is what makes the frame number well defined: `pfn` is exact division, not
//! a truncation that quietly loses a byte offset.
//!
//! The size is a type parameter rather than a field, so a 4 KiB frame and a
//! 2 MiB frame are different types and the same physical address has a
//! different frame number in each -- as it should, since the two sizes number
//! memory differently.
//!
//! The iterator impls of the original are deliberately absent: this crate has
//! no verified `Iterator` machinery, and a loop that needs one can drive
//! [`PhysFrameRange::len`] with an index instead.
use core::marker::PhantomData;

use builtin_macros::*;
use vstd::prelude::*;

use crate::structs::address::{Address, PhysAddr};
use crate::structs::page::AddressNotAligned;
use crate::structs::sizes::{PageSize, Size4KiB};

#[cfg(verus_only)]
include!("../specs/frame.rs");

/// A physical memory frame of size `S`.
#[verus_verify]
#[repr(C)]
pub struct PhysFrame<S: PageSize = Size4KiB> {
    start_address: PhysAddr,
    size: PhantomData<S>,
}

/// A frame number whose frame does not fit in a physical address.
#[verus_verify(external_derive)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct PfnNotValid(pub usize);

#[verus_verify]
impl<S: PageSize> PhysFrame<S> {
    /// The frame starting at `address`, or an error if that address is not the
    /// start of a frame.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.is_ok() == is_aligned_spec(address@, S::SIZE),
            ret.is_ok() ==> ret.unwrap()@ == address@,
    )]
    pub fn from_start_address(address: PhysAddr) -> Result<Self, AddressNotAligned> {
        if !address.is_page_aligned::<S>() {
            return Err(AddressNotAligned);
        }
        proof! { S::lemma_size_wf(); }
        Ok(PhysFrame { start_address: address, size: PhantomData })
    }

    /// The frame starting at `start_address`.
    ///
    /// Unlike the original this is safe: the alignment the `unsafe` version
    /// asks the caller to guarantee is stated as a precondition instead, so it
    /// is checked rather than trusted.
    #[inline]
    #[verus_spec(ret =>
        requires
            is_aligned_spec(start_address@, S::SIZE),
        ensures
            ret@ == start_address@,
    )]
    pub fn from_start_address_unchecked(start_address: PhysAddr) -> Self {
        proof! { S::lemma_size_wf(); }
        PhysFrame { start_address, size: PhantomData }
    }

    /// The frame with the given frame number, or an error if numbering that
    /// far overflows a physical address.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.is_ok() == (pfn * S::SIZE <= usize::MAX),
            ret.is_ok() ==> ret.unwrap()@ == pfn * S::SIZE,
    )]
    pub fn try_from_pfn(pfn: usize) -> Result<Self, PfnNotValid> {
        proof! { S::lemma_size_wf(); }
        match pfn.checked_mul(S::SIZE) {
            Some(addr) => {
                proof! {
                    lemma_phys_addr_from_bits(addr);
                    lemma_mul_mod_zero(pfn as int, S::SIZE as int);
                }
                Ok(PhysFrame { start_address: PhysAddr::from(addr), size: PhantomData })
            },
            None => Err(PfnNotValid(pfn)),
        }
    }

    /// The frame with the given frame number.
    #[inline]
    #[verus_spec(ret =>
        requires
            pfn * S::SIZE <= usize::MAX,
        ensures
            ret@ == pfn * S::SIZE,
    )]
    pub fn from_pfn(pfn: usize) -> Self {
        match Self::try_from_pfn(pfn) {
            Ok(frame) => frame,
            Err(_) => panic!("frame number too large for a physical address"),
        }
    }

    /// The frame containing `address`.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret@ == address@ - address@ % S::SIZE,
    )]
    pub fn containing_address(address: PhysAddr) -> Self {
        proof! { S::lemma_size_wf(); }
        let bits = address.bits();
        proof! { lemma_mod_decreases(bits as nat, S::SIZE as nat); }
        let start = bits - bits % S::SIZE;
        proof! {
            lemma_phys_addr_from_bits(start);
            lemma_align_down_is_aligned(bits as int, S::SIZE as int);
        }
        PhysFrame { start_address: PhysAddr::from(start), size: PhantomData }
    }

    /// The address this frame starts at.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret@ == self@,
    )]
    pub fn start_address(self) -> PhysAddr {
        self.start_address
    }

    /// The size of this frame in bytes.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == S::SIZE,
    )]
    pub fn size(self) -> usize {
        S::SIZE
    }

    /// This frame's number: its start address divided by the frame size.
    ///
    /// The same address has a different number at each size, because each size
    /// numbers memory in units of itself.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_pfn(),
    )]
    pub fn pfn(self) -> usize {
        proof! { S::lemma_size_wf(); }
        self.start_address.bits() / S::SIZE
    }

    /// The frames from `start` up to, but not including, `end`.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.start == start,
            ret.end == end,
    )]
    pub fn range(start: PhysFrame<S>, end: PhysFrame<S>) -> PhysFrameRange<S> {
        PhysFrameRange { start, end }
    }

    /// The frames from `start` up to and including `end`.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret.start == start,
            ret.end == end,
    )]
    pub fn range_inclusive(start: PhysFrame<S>, end: PhysFrame<S>) -> PhysFrameRangeInclusive<S> {
        PhysFrameRangeInclusive { start, end }
    }
}

/// A range of physical frames, `end` exclusive.
#[verus_verify]
#[repr(C)]
pub struct PhysFrameRange<S: PageSize = Size4KiB> {
    /// The first frame of the range.
    pub start: PhysFrame<S>,
    /// The frame after the last one of the range.
    pub end: PhysFrame<S>,
}

#[verus_verify]
impl<S: PageSize> PhysFrameRange<S> {
    /// Whether the range holds no frames.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == (self.start@ >= self.end@),
    )]
    pub fn is_empty(&self) -> bool {
        self.start.start_address().bits() >= self.end.start_address().bits()
    }

    /// The number of frames in the range.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_len(),
    )]
    pub fn len(&self) -> usize {
        if !self.is_empty() {
            proof! { lemma_pfn_ordered(self.start, self.end); }
            self.end.pfn() - self.start.pfn()
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

/// A range of physical frames, `end` inclusive.
#[verus_verify]
#[repr(C)]
pub struct PhysFrameRangeInclusive<S: PageSize = Size4KiB> {
    /// The first frame of the range.
    pub start: PhysFrame<S>,
    /// The last frame of the range.
    pub end: PhysFrame<S>,
}

#[verus_verify]
impl<S: PageSize> PhysFrameRangeInclusive<S> {
    /// Whether the range holds no frames.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == (self.start@ > self.end@),
    )]
    pub fn is_empty(&self) -> bool {
        self.start.start_address().bits() > self.end.start_address().bits()
    }

    /// The number of frames in the range.
    #[inline]
    #[verus_spec(ret =>
        ensures
            ret == self.spec_len(),
    )]
    pub fn len(&self) -> usize {
        if !self.is_empty() {
            proof! {
                lemma_pfn_ordered(self.start, self.end);
                lemma_pfn_lt_max(self.end);
            }
            self.end.pfn() - self.start.pfn() + 1
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

// `derive(Copy)` would demand `S: Copy`, which a size marker has no reason to
// be: it is never a value, only a name for a number.
impl<S: PageSize> Clone for PhysFrame<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for PhysFrame<S> {}

impl<S: PageSize> Clone for PhysFrameRange<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for PhysFrameRange<S> {}

impl<S: PageSize> Clone for PhysFrameRangeInclusive<S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: PageSize> Copy for PhysFrameRangeInclusive<S> {}

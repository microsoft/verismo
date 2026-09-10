// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
use crate::structs::sizes::{PageOffset, PageSize, Size4KiB};
use crate::util::{align_down, align_up, is_aligned};

use core::fmt;
use core::ops;
use core::ptr::NonNull;
use core::slice;

// The backing type to represent an address;
type InnerAddr = usize;

const SIGN_BIT: usize = 47;

#[inline]
const fn sign_extend(addr: InnerAddr) -> InnerAddr {
    let mask = 1usize << SIGN_BIT;
    if (addr & mask) == mask {
        addr | !((1usize << SIGN_BIT) - 1)
    } else {
        addr & ((1usize << SIGN_BIT) - 1)
    }
}

pub trait Address: Copy + From<InnerAddr> + Into<InnerAddr> + Ord {
    /// Transform the address into its inner representation for easier
    /// arithmetic manipulation
    #[inline]
    fn bits(&self) -> InnerAddr {
        (*self).into()
    }

    #[inline]
    fn is_null(&self) -> bool {
        self.bits() == 0
    }

    #[inline]
    fn align_up(&self, align: InnerAddr) -> Self {
        Self::from(align_up(self.bits(), align))
    }

    #[inline]
    fn align_down(&self, align: InnerAddr) -> Self {
        Self::from(align_down(self.bits(), align))
    }

    #[inline]
    fn page_align_up<S: PageSize>(&self) -> Self {
        self.align_up(S::SIZE)
    }

    #[inline]
    fn page_align<S: PageSize>(&self) -> Self {
        self.align_down(S::SIZE)
    }

    #[inline]
    fn is_aligned(&self, align: InnerAddr) -> bool {
        is_aligned(self.bits(), align)
    }

    #[inline]
    fn is_aligned_to<T>(&self) -> bool {
        self.is_aligned(core::mem::align_of::<T>())
    }

    #[inline]
    fn is_page_aligned<S: PageSize>(&self) -> bool {
        self.is_aligned(S::SIZE)
    }

    #[inline]
    fn checked_add(&self, off: InnerAddr) -> Option<Self> {
        self.bits().checked_add(off).map(|addr| addr.into())
    }

    #[inline]
    fn checked_sub(&self, off: InnerAddr) -> Option<Self> {
        self.bits().checked_sub(off).map(|addr| addr.into())
    }

    #[inline]
    fn saturating_add(&self, off: InnerAddr) -> Self {
        Self::from(self.bits().saturating_add(off))
    }

    #[inline]
    fn page_offset<S: PageSize>(&self) -> usize {
        self.bits() & (S::SIZE - 1)
    }

    #[inline]
    fn crosses_page(&self, size: usize) -> bool {
        let start = self.bits();
        let x1 = start / <Size4KiB as PageSize>::SIZE;
        let x2 = (start + (size - 1)) / <Size4KiB as PageSize>::SIZE;
        x1 != x2
    }

    #[inline]
    fn pfn(&self) -> InnerAddr {
        self.bits() >> <Size4KiB as PageOffset>::SHIFT
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PhysAddr(InnerAddr);

impl PhysAddr {
    #[inline]
    pub const fn new(p: InnerAddr) -> Self {
        Self(p)
    }

    #[inline]
    pub const fn null() -> Self {
        Self(0)
    }
}

impl fmt::Display for PhysAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::LowerHex for PhysAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl From<InnerAddr> for PhysAddr {
    #[inline]
    fn from(addr: InnerAddr) -> PhysAddr {
        Self(addr)
    }
}

impl From<PhysAddr> for InnerAddr {
    #[inline]
    fn from(addr: PhysAddr) -> InnerAddr {
        addr.0
    }
}

impl From<u64> for PhysAddr {
    #[inline]
    fn from(addr: u64) -> PhysAddr {
        // The unwrap will get optimized away on 64bit platforms,
        // which should be our only target anyway
        let addr: usize = addr.try_into().unwrap();
        PhysAddr::from(addr)
    }
}

impl From<PhysAddr> for u64 {
    #[inline]
    fn from(addr: PhysAddr) -> u64 {
        addr.0 as u64
    }
}

// Substracting two addresses produces an usize instead of an address,
// since we normally do this to compute the size of a memory region.
impl ops::Sub<PhysAddr> for PhysAddr {
    type Output = InnerAddr;

    #[inline]
    fn sub(self, other: PhysAddr) -> Self::Output {
        self.0 - other.0
    }
}

// Adding and subtracting usize to PhysAddr gives a new PhysAddr
impl ops::Sub<InnerAddr> for PhysAddr {
    type Output = Self;

    #[inline]
    fn sub(self, other: InnerAddr) -> Self {
        PhysAddr::from(self.0 - other)
    }
}

impl ops::Add<InnerAddr> for PhysAddr {
    type Output = Self;

    #[inline]
    fn add(self, other: InnerAddr) -> Self {
        PhysAddr::from(self.0 + other)
    }
}

impl Address for PhysAddr {}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct VirtAddr(InnerAddr);

impl VirtAddr {
    #[inline]
    pub const fn null() -> Self {
        Self(0)
    }

    // const traits experimental, so for now we need this to make up
    // for the lack of VirtAddr::from() in const contexts.
    #[inline]
    pub const fn new(addr: InnerAddr) -> Self {
        Self(sign_extend(addr))
    }

    /// The shift and mask encode x86-64's paging geometry; this belongs with
    /// that architecture's code, but moving it is deferred to avoid rippling
    /// through callers here.
    pub const fn to_pgtbl_idx<const L: usize>(&self) -> usize {
        (self.0 >> (12 + L * 9)) & 0x1ffusize
    }

    #[inline]
    pub fn as_ptr<T>(&self) -> *const T {
        core::ptr::with_exposed_provenance(self.0)
    }

    #[inline]
    pub fn as_mut_ptr<T>(&self) -> *mut T {
        core::ptr::with_exposed_provenance_mut(self.0)
    }

    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0
    }

    /// A reference to the `T` here, or `None` if null or misaligned.
    ///
    /// # Safety
    /// Every pointer requirement but alignment and null applies.
    #[inline]
    pub unsafe fn aligned_ref<'a, T>(&self) -> Option<&'a T> {
        self.is_aligned_to::<T>()
            // SAFETY: caller should already provide safety requirements for
            // pointers that should be null or convertible to a reference.
            .then(|| unsafe { self.as_ptr::<T>().as_ref() })
            .flatten()
    }

    /// A mutable reference to the `T` here, or `None` if null or misaligned.
    ///
    /// # Safety
    /// Every pointer requirement but alignment and null applies.
    #[inline]
    pub unsafe fn aligned_mut<'a, T>(&self) -> Option<&'a mut T> {
        self.is_aligned_to::<T>()
            // SAFETY: caller should already provide safety requirements for
            // pointers that should be null or convertible to a reference.
            .then(|| unsafe { self.as_mut_ptr::<T>().as_mut() })
            .flatten()
    }

    pub const fn const_add(&self, offset: usize) -> Self {
        VirtAddr::new(self.0 + offset)
    }

    pub const fn const_sub(&self, offset: usize) -> Self {
        VirtAddr::new(self.0 - offset)
    }

    /// The `len` values of type `T` starting here.
    ///
    /// # Safety
    /// As for [`core::slice::from_raw_parts`].
    pub unsafe fn to_slice<T>(&self, len: usize) -> &[T] {
        // SAFETY: caller should already provide safety requirements for
        // [`core::slice::from_raw_parts`]
        unsafe { slice::from_raw_parts::<T>(self.as_ptr::<T>(), len) }
    }
}

impl fmt::Display for VirtAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::LowerHex for VirtAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::LowerHex::fmt(&self.0, f)
    }
}

impl From<InnerAddr> for VirtAddr {
    #[inline]
    fn from(addr: InnerAddr) -> Self {
        Self(sign_extend(addr))
    }
}

impl From<VirtAddr> for InnerAddr {
    #[inline]
    fn from(addr: VirtAddr) -> Self {
        addr.0
    }
}

impl From<u64> for VirtAddr {
    #[inline]
    fn from(addr: u64) -> Self {
        let addr: usize = addr.try_into().unwrap();
        VirtAddr::from(addr)
    }
}

impl From<VirtAddr> for u64 {
    #[inline]
    fn from(addr: VirtAddr) -> Self {
        addr.0 as u64
    }
}

impl<T> From<*const T> for VirtAddr {
    #[inline]
    fn from(ptr: *const T) -> Self {
        Self::from(ptr as InnerAddr)
    }
}

impl<T> From<*mut T> for VirtAddr {
    fn from(ptr: *mut T) -> Self {
        Self::from(ptr as InnerAddr)
    }
}

impl<T> From<NonNull<T>> for VirtAddr {
    #[inline]
    fn from(value: NonNull<T>) -> Self {
        Self::from(value.as_ptr())
    }
}

impl ops::Sub<VirtAddr> for VirtAddr {
    type Output = InnerAddr;

    #[inline]
    fn sub(self, other: VirtAddr) -> InnerAddr {
        (self.0 - other.0) & ((1usize << (SIGN_BIT + 1)) - 1)
    }
}

impl ops::Sub<usize> for VirtAddr {
    type Output = Self;

    #[inline]
    fn sub(self, other: usize) -> Self {
        VirtAddr::from(self.0 - other)
    }
}

impl ops::Add<InnerAddr> for VirtAddr {
    type Output = VirtAddr;

    fn add(self, other: InnerAddr) -> Self {
        VirtAddr::from(self.0 + other)
    }
}

impl Address for VirtAddr {
    #[inline]
    fn checked_add(&self, off: InnerAddr) -> Option<Self> {
        self.bits().checked_add(off).map(|addr| sign_extend(addr).into())
    }

    #[inline]
    fn checked_sub(&self, off: InnerAddr) -> Option<Self> {
        self.bits().checked_sub(off).map(|addr| sign_extend(addr).into())
    }
}

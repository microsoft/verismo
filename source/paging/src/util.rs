// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC

use crate::structs::sizes::{PageSize, Regular};
use core::ops::{Add, BitAnd, Not, Sub};

pub fn align_up<T>(addr: T, align: T) -> T
where
    T: Add<Output = T> + Sub<Output = T> + BitAnd<Output = T> + Not<Output = T> + From<u8> + Copy,
{
    let mask: T = align - T::from(1u8);
    (addr + mask) & !mask
}

pub fn align_down<T>(addr: T, align: T) -> T
where
    T: Sub<Output = T> + Not<Output = T> + BitAnd<Output = T> + From<u8> + Copy,
{
    addr & !(align - T::from(1u8))
}

pub fn is_aligned<T>(addr: T, align: T) -> bool
where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
{
    (addr & (align - T::from(1u8))) == T::from(0u8)
}

pub fn page_align_up(x: usize) -> usize {
    align_up(x, <Regular as PageSize>::SIZE)
}

pub fn round_to_pages(x: usize) -> usize {
    page_align_up(x) / <Regular as PageSize>::SIZE
}

pub fn page_offset(x: usize) -> usize {
    x & (<Regular as PageSize>::SIZE - 1)
}

pub fn overlap<T>(x1: T, x2: T, y1: T, y2: T) -> bool
where
    T: PartialOrd,
{
    x1 <= y2 && y1 <= x2
}

#[cfg(test)]
#[path = "../tests/unit/util.rs"]
mod tests;

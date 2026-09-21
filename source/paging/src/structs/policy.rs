//! Mutation authority and ownership of subtrees below an owned root.

use core::marker::PhantomData;

use crate::structs::address::{Address, VirtAddr, LOW_CANONICAL_END};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingError;
use crate::structs::sizes::entry_index;
use crate::structs::sizes::PT_ENTRY_COUNT;

mod sealed {
    /// Prevents downstream crates from defining paging ownership policies.
    pub trait Sealed {}
}

/// Authorizes address mutations and selects which top-level subtrees are owned.
pub trait PagingOwnershipPolicy: sealed::Sealed {
    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError>;
    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError>;
    fn owns_top_entry(&self, index: usize) -> bool;
}

/// Privileged access to the whole tree; every attached subtree is owned.
#[derive(Clone, Copy, Debug, Default)]
pub struct KernelPolicy;

/// Selects immutable, non-owned entries in a user page table's root.
pub trait RootEntrySet: sealed::Sealed {
    /// Returns whether `index` belongs to this set.
    fn contains(index: usize) -> bool;

    #[doc(hidden)]
    fn valid() -> bool;
}

/// Root entries in the half-open interval `START..END`.
#[derive(Clone, Copy, Debug, Default)]
pub struct RootRange<const START: usize, const END: usize>;

/// The union of two root-entry sets.
#[derive(Clone, Copy, Debug, Default)]
pub struct RootUnion<Left, Right>(PhantomData<(Left, Right)>);

/// Zero-sized policy reserving `Reserved` as immutable, non-owned kernel entries.
#[derive(Debug)]
pub struct UserPolicy<'kernel, Reserved: RootEntrySet> {
    kernel: PhantomData<&'kernel Reserved>,
}

impl<Reserved: RootEntrySet> UserPolicy<'_, Reserved> {
    pub(crate) fn new() -> Self {
        assert!(Reserved::valid());
        Self { kernel: PhantomData }
    }

    /// Returns whether this policy borrows the root entry from its kernel owner.
    pub fn borrows_top_entry(&self, index: usize) -> bool {
        assert!(index < PT_ENTRY_COUNT);
        Reserved::contains(index)
    }

    fn check_segment(&self, root: PageLevel, first: usize, last: usize) -> Result<(), PagingError> {
        let first_page = first / root.size();
        let last_page = last / root.size();
        if last_page - first_page >= PT_ENTRY_COUNT {
            return if (0..PT_ENTRY_COUNT).any(Reserved::contains) {
                Err(PagingError::PermissionDenied)
            } else {
                Ok(())
            };
        }
        let mut page = first_page;
        loop {
            if Reserved::contains(page % PT_ENTRY_COUNT) {
                return Err(PagingError::PermissionDenied);
            }
            if page == last_page {
                return Ok(());
            }
            page += 1;
        }
    }
}

impl sealed::Sealed for KernelPolicy {}
impl<const START: usize, const END: usize> sealed::Sealed for RootRange<START, END> {}
impl<Left: RootEntrySet, Right: RootEntrySet> sealed::Sealed for RootUnion<Left, Right> {}
impl<Reserved: RootEntrySet> sealed::Sealed for UserPolicy<'_, Reserved> {}

impl<const START: usize, const END: usize> RootEntrySet for RootRange<START, END> {
    fn contains(index: usize) -> bool {
        START <= index && index < END
    }

    fn valid() -> bool {
        START <= END && END <= PT_ENTRY_COUNT
    }
}

impl<Left: RootEntrySet, Right: RootEntrySet> RootEntrySet for RootUnion<Left, Right> {
    fn contains(index: usize) -> bool {
        Left::contains(index) || Right::contains(index)
    }

    fn valid() -> bool {
        Left::valid() && Right::valid()
    }
}

impl PagingOwnershipPolicy for KernelPolicy {
    fn check_address(&self, _root: PageLevel, _address: VirtAddr) -> Result<(), PagingError> {
        Ok(())
    }

    fn check_range(
        &self,
        _root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError> {
        if start > end {
            Err(PagingError::InvalidRange)
        } else {
            Ok(())
        }
    }

    fn owns_top_entry(&self, index: usize) -> bool {
        assert!(index < PT_ENTRY_COUNT);
        true
    }
}

impl<Reserved: RootEntrySet> PagingOwnershipPolicy for UserPolicy<'_, Reserved> {
    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError> {
        if Reserved::contains(entry_index(address, root)) {
            Err(PagingError::PermissionDenied)
        } else {
            Ok(())
        }
    }

    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError> {
        if start > end {
            return Err(PagingError::InvalidRange);
        }
        if start == end {
            return Ok(());
        }
        let last = VirtAddr::from(end.bits() - 1).bits();
        if start.bits() < LOW_CANONICAL_END && last >= LOW_CANONICAL_END {
            self.check_segment(root, start.bits(), LOW_CANONICAL_END - 1)?;
            self.check_segment(root, VirtAddr::from(LOW_CANONICAL_END).bits(), last)
        } else {
            self.check_segment(root, start.bits(), last)
        }
    }

    fn owns_top_entry(&self, index: usize) -> bool {
        !self.borrows_top_entry(index)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/policy.rs"]
mod tests;

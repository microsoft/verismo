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
    #[doc(hidden)]
    type Owned: OwnedIndices;

    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError>;
    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError>;
    /// Returns whether every root entry intersecting `start..end` is owned.
    fn owns_range(&self, root: PageLevel, start: VirtAddr, end: VirtAddr) -> bool;
    fn owns_top_entry(&self, index: usize) -> bool;
}

/// Selects the root entries owned and mutable through a page-table controller.
pub trait OwnedIndices: sealed::Sealed {
    #[doc(hidden)]
    const ASSERT_VALID: ();
    #[doc(hidden)]
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64];

    /// Returns whether `index` belongs to this set.
    fn contains(index: usize) -> bool;
}

/// Root entries in the non-empty half-open interval `START..END`.
///
/// ```compile_fail,E0080
/// use paging::policy::{CoveredRange, OwnedIndices};
///
/// const INVALID: () = <CoveredRange<2, 2> as OwnedIndices>::ASSERT_VALID;
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct CoveredRange<const START: usize, const END: usize>;

/// The union of two disjoint covered ranges.
///
/// ```compile_fail,E0080
/// use paging::policy::{CoveredRange, OwnedIndices, RootUnion};
///
/// type Overlapping = RootUnion<CoveredRange<1, 4>, CoveredRange<3, 6>>;
///
/// const INVALID: () = <Overlapping as OwnedIndices>::ASSERT_VALID;
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct RootUnion<Left, Right>(PhantomData<(Left, Right)>);

/// All root entries outside `Set`.
#[derive(Clone, Copy, Debug, Default)]
pub struct RootComplement<Set>(PhantomData<Set>);

/// An empty root-entry set.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoRootEntries;

/// Every root entry.
#[derive(Clone, Copy, Debug, Default)]
pub struct AllRootEntries;

/// Zero-sized policy owning exactly the entries selected by `Owned`.
#[derive(Debug)]
pub struct Policy<Owned: OwnedIndices> {
    owned: PhantomData<Owned>,
}

impl<Owned: OwnedIndices> Clone for Policy<Owned> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Owned: OwnedIndices> Copy for Policy<Owned> {}

impl<Owned: OwnedIndices> Default for Policy<Owned> {
    fn default() -> Self {
        Self::new()
    }
}

/// A kernel root-ownership policy.
pub type KernelPolicy<Owned = AllRootEntries> = Policy<Owned>;

/// A user root-ownership policy.
pub type UserPolicy<Owned> = Policy<Owned>;

impl<Owned: OwnedIndices> Policy<Owned> {
    pub(crate) fn new() -> Self {
        let () = Owned::ASSERT_VALID;
        Self { owned: PhantomData }
    }

    /// Returns whether this policy borrows the root entry from its kernel owner.
    pub fn borrows_top_entry(&self, index: usize) -> bool {
        assert!(index < PT_ENTRY_COUNT);
        !Owned::contains(index)
    }

    fn owns_index_range(start: usize, end: usize) -> bool {
        let first_word = start / 64;
        let last_word = (end - 1) / 64;
        for word in first_word..=last_word {
            let first_bit = if word == first_word { start % 64 } else { 0 };
            let end_bit = if word == last_word { (end - 1) % 64 + 1 } else { 64 };
            let lower = u64::MAX << first_bit;
            let upper = if end_bit == 64 { u64::MAX } else { (1 << end_bit) - 1 };
            let required = lower & upper;
            if Owned::ROOT_MASK[word] & required != required {
                return false;
            }
        }
        true
    }

    fn owns_segment(root: PageLevel, first: usize, last: usize) -> bool {
        let first_page = first / root.size();
        let last_page = last / root.size();
        if last_page - first_page >= PT_ENTRY_COUNT - 1 {
            return Owned::ROOT_MASK.iter().all(|word| *word == u64::MAX);
        }
        let first_index = first_page % PT_ENTRY_COUNT;
        let end_index = last_page % PT_ENTRY_COUNT + 1;
        if first_page / PT_ENTRY_COUNT == last_page / PT_ENTRY_COUNT {
            Self::owns_index_range(first_index, end_index)
        } else {
            Self::owns_index_range(first_index, PT_ENTRY_COUNT)
                && Self::owns_index_range(0, end_index)
        }
    }
}

impl sealed::Sealed for NoRootEntries {}
impl sealed::Sealed for AllRootEntries {}
impl<const START: usize, const END: usize> sealed::Sealed for CoveredRange<START, END> {}
impl<Left: OwnedIndices, Right: OwnedIndices> sealed::Sealed for RootUnion<Left, Right> {}
impl<Set: OwnedIndices> sealed::Sealed for RootComplement<Set> {}
impl<Owned: OwnedIndices> sealed::Sealed for Policy<Owned> {}

impl OwnedIndices for NoRootEntries {
    const ASSERT_VALID: () = ();
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = [0; PT_ENTRY_COUNT / 64];

    fn contains(_index: usize) -> bool {
        false
    }
}

impl OwnedIndices for AllRootEntries {
    const ASSERT_VALID: () = ();
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = [u64::MAX; PT_ENTRY_COUNT / 64];

    fn contains(index: usize) -> bool {
        index < PT_ENTRY_COUNT
    }
}

impl<const START: usize, const END: usize> OwnedIndices for CoveredRange<START, END> {
    const ASSERT_VALID: () = {
        assert!(START < END);
        assert!(END <= PT_ENTRY_COUNT);
    };
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = root_mask(START, END);

    fn contains(index: usize) -> bool {
        START <= index && index < END
    }
}

impl<Left: OwnedIndices, Right: OwnedIndices> OwnedIndices for RootUnion<Left, Right> {
    const ASSERT_VALID: () = {
        let () = CoveragePair::<Left, Right>::ASSERT_DISJOINT;
    };
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = union_mask(Left::ROOT_MASK, Right::ROOT_MASK);

    fn contains(index: usize) -> bool {
        Left::contains(index) || Right::contains(index)
    }
}

impl<Set: OwnedIndices> OwnedIndices for RootComplement<Set> {
    const ASSERT_VALID: () = Set::ASSERT_VALID;
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = complement_mask(Set::ROOT_MASK);

    fn contains(index: usize) -> bool {
        !Set::contains(index)
    }
}

struct CoveragePair<Left, Right>(PhantomData<(Left, Right)>);

impl<Left: OwnedIndices, Right: OwnedIndices> CoveragePair<Left, Right> {
    const ASSERT_DISJOINT: () = {
        let () = Left::ASSERT_VALID;
        let () = Right::ASSERT_VALID;
        let mut index = 0;
        while index < Left::ROOT_MASK.len() {
            assert!(Left::ROOT_MASK[index] & Right::ROOT_MASK[index] == 0);
            index += 1;
        }
    };
}

/// Asserts at compile time that two policies cover disjoint root entries.
///
/// ```compile_fail,E0080
/// use paging::policy::{assert_disjoint_policies, CoveredRange, KernelPolicy};
///
/// type Left = KernelPolicy<CoveredRange<1, 4>>;
/// type Right = KernelPolicy<CoveredRange<3, 6>>;
///
/// const INVALID: () = assert_disjoint_policies::<Left, Right>();
/// ```
pub const fn assert_disjoint_policies<Left, Right>()
where
    Left: PagingOwnershipPolicy,
    Right: PagingOwnershipPolicy,
{
    let () = CoveragePair::<Left::Owned, Right::Owned>::ASSERT_DISJOINT;
}

pub(crate) fn assert_borrowed_disjoint_from<Source, Owned>(_source: &Source)
where
    Source: PagingOwnershipPolicy,
    Owned: OwnedIndices,
{
    let () = BorrowedCoveragePair::<Source::Owned, Owned>::ASSERT_DISJOINT;
}

struct BorrowedCoveragePair<Left, Right>(PhantomData<(Left, Right)>);

impl<Left: OwnedIndices, Right: OwnedIndices> BorrowedCoveragePair<Left, Right> {
    const ASSERT_DISJOINT: () = {
        let () = Left::ASSERT_VALID;
        let () = Right::ASSERT_VALID;
        let mut index = 0;
        while index < Left::ROOT_MASK.len() {
            assert!((!Left::ROOT_MASK[index]) & (!Right::ROOT_MASK[index]) == 0);
            index += 1;
        }
    };
}

const fn root_mask(start: usize, end: usize) -> [u64; PT_ENTRY_COUNT / 64] {
    assert!(start < end);
    assert!(end <= PT_ENTRY_COUNT);
    let mut mask = [0; PT_ENTRY_COUNT / 64];
    let mut index = start;
    while index < end {
        mask[index / 64] |= 1 << (index % 64);
        index += 1;
    }
    mask
}

const fn union_mask(
    left: [u64; PT_ENTRY_COUNT / 64],
    right: [u64; PT_ENTRY_COUNT / 64],
) -> [u64; PT_ENTRY_COUNT / 64] {
    let mut mask = [0; PT_ENTRY_COUNT / 64];
    let mut index = 0;
    while index < mask.len() {
        mask[index] = left[index] | right[index];
        index += 1;
    }
    mask
}

const fn complement_mask(source: [u64; PT_ENTRY_COUNT / 64]) -> [u64; PT_ENTRY_COUNT / 64] {
    let mut mask = [0; PT_ENTRY_COUNT / 64];
    let mut index = 0;
    while index < mask.len() {
        mask[index] = !source[index];
        index += 1;
    }
    mask
}

impl<Owned: OwnedIndices> PagingOwnershipPolicy for Policy<Owned> {
    type Owned = Owned;

    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError> {
        if Owned::contains(entry_index(address, root)) {
            Ok(())
        } else {
            Err(PagingError::PermissionDenied)
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
        if self.owns_range(root, start, end) {
            return Ok(());
        }
        Err(PagingError::PermissionDenied)
    }

    fn owns_range(&self, root: PageLevel, start: VirtAddr, end: VirtAddr) -> bool {
        if start > end {
            return false;
        }
        if start == end {
            return true;
        }
        let last = VirtAddr::from(end.bits() - 1).bits();
        if start.bits() < LOW_CANONICAL_END && last >= LOW_CANONICAL_END {
            Self::owns_segment(root, start.bits(), LOW_CANONICAL_END - 1)
                && Self::owns_segment(root, VirtAddr::from(LOW_CANONICAL_END).bits(), last)
        } else {
            Self::owns_segment(root, start.bits(), last)
        }
    }

    fn owns_top_entry(&self, index: usize) -> bool {
        assert!(index < PT_ENTRY_COUNT);
        Owned::contains(index)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/policy.rs"]
mod tests;

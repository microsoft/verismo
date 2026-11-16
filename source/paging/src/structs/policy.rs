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

    /// Whether a table using this policy may be shared from through
    /// [`PageTable::new_from_sharing_top`]/[`PageTable::populate_shared`] at
    /// all. Checked at compile time: only policies with this set to `true`
    /// implement [`MayShareSubtree`], which those constructors require of
    /// their source policy.
    ///
    /// [`PageTable::new_from_sharing_top`]: crate::pagetable::PageTable::new_from_sharing_top
    /// [`PageTable::populate_shared`]: crate::pagetable::PageTable::populate_shared
    const MAY_SHARE_SUBTREE: bool;

    /// Which of this policy's page-table pages may ever be freed while a
    /// borrow could still exist, selecting whether the sharing constructors
    /// and the reclaim paths maintain and consult
    /// [`PagingAllocator::share_count`] tracking for them. See
    /// [`MayFreePageTablePages`]'s variants for what each of `Owned`,
    /// `Shared`, `All`, and `No` means.
    ///
    /// A sharing constructor asserts at compile time that the derived
    /// table's [`MayFreePageTablePages::frees_shared`] agrees with its
    /// source's [`MayFreePageTablePages::frees_owned`], so [`PTPageTree`]'s
    /// `Drop` can later read only its own policy's value and still make the
    /// same tracking decision the constructor made.
    ///
    /// # Enforcement
    ///
    /// `frees_owned() == false` is actively enforced by `Drop`: it leaks
    /// (never frees) this policy's owned top-level entries instead of
    /// trusting the declared value, so understating it (claiming `false`
    /// when a table could otherwise free a shared top-level page) only
    /// leaks memory, never frees a page while it could still be shared.
    /// `frees_owned() == true` is checked instead: `Drop` asserts
    /// [`PagingAllocator::share_count`] is zero for each owned top-level
    /// entry before freeing it, panicking if a derived table still shares
    /// it. Neither branch relies purely on the declared value being honest;
    /// only the compile-time-unreachable case of a genuine time-of-check to
    /// time-of-use race (freeing concurrently with a sharing constructor's
    /// read-then-increment) or a source and consumer that entirely bypass
    /// `share_count` themselves remain outside these checks.
    ///
    /// [`PagingAllocator::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
    /// [`PTPageTree`]: crate::structs::ptpage::PTPageTree
    const MAY_FREE_PAGE_TABLE_PAGES: MayFreePageTablePages;

    /// Checks whether `address` is valid for `root`.
    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError>;

    /// Checks whether the range `start..end` is valid for `root`.
    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError>;

    /// Returns whether every root entry intersecting `start..end` is owned.
    fn owns_range(&self, root: PageLevel, start: VirtAddr, end: VirtAddr) -> bool;

    /// Returns whether the top-level entry at `index` is owned.
    fn owns_top_entry(&self, index: usize) -> bool;
}

/// Which of a policy's page-table pages may ever be freed while a table
/// derived from it (or that it was derived from) could still be observing
/// them.
///
/// Stable Rust cannot yet use a plain enum as a const generic parameter (see
/// [`rust-lang/rust#95174`](https://github.com/rust-lang/rust/issues/95174)),
/// so [`Policy`] instead takes the packed bits selecting one of these
/// variants; read [`PagingOwnershipPolicy::MAY_FREE_PAGE_TABLE_PAGES`] back
/// through this type instead of matching on raw bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum MayFreePageTablePages {
    /// Neither this table's own (owned) page-table pages nor anything it
    /// borrows from another table are ever freed while shared: no
    /// [`PagingAllocator::share_count`] tracking is needed in either
    /// direction.
    ///
    /// [`PagingAllocator::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
    No = 0,
    /// This table's own (owned) page-table pages may be freed by this table,
    /// but nothing it borrows from another table is ever freed by that
    /// source while shared: only the increment/refusal-check side of
    /// tracking applies (this table is a possible sharing source, never a
    /// borrower of pages that go away).
    Owned = 1,
    /// This table never frees its own (owned) page-table pages, but the
    /// tables it borrows subtrees from may free theirs while shared, so this
    /// table must track and release its share of every borrowed entry (at
    /// `Drop` or [`PageTable::release_shared`]).
    ///
    /// [`PageTable::release_shared`]: crate::pagetable::PageTable::release_shared
    Shared = 2,
    /// Both: this table's own page-table pages may be freed, and the
    /// sources it borrows from may free theirs too. The conservative
    /// default.
    All = 3,
}

impl MayFreePageTablePages {
    /// Whether this table's own (owned) page-table pages may be freed while shared.
    pub const fn frees_owned(self) -> bool {
        matches!(self, Self::Owned | Self::All)
    }

    /// Whether this table must track and release its share of borrowed
    /// (non-owned) entries, because their source may free them while shared.
    pub const fn frees_shared(self) -> bool {
        matches!(self, Self::Shared | Self::All)
    }

    /// Recovers a variant from [`Policy`]'s packed const-generic bits.
    pub(crate) const fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::No,
            1 => Self::Owned,
            2 => Self::Shared,
            3 => Self::All,
            _ => panic!("invalid MayFreePageTablePages bits"),
        }
    }
}

/// Selects the root entries owned and mutable through a page-table controller.
pub trait OwnedIndices: sealed::Sealed {
    #[doc(hidden)]
    const ASSERT_VALID: ();
    #[doc(hidden)]
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64];

    /// Returns whether every index in the non-empty half-open range
    /// `start..end` belongs to this set. Implemented once here, in terms of
    /// [`Self::ROOT_MASK`], word-at-a-time, rather than per-implementor, so
    /// no `OwnedIndices` impl needs to reimplement range containment.
    ///
    /// Time complexity: `O(last_word - first_word + 1)`, i.e. one iteration
    /// per 64-bit word of [`Self::ROOT_MASK`] the query range touches. Since
    /// `Self::ROOT_MASK` has exactly `PT_ENTRY_COUNT / 64` (8) words, this is
    /// bounded by 8 iterations regardless of how many sub-ranges make up
    /// `Self` (e.g. how deeply a [`RootUnion`]/[`RootComplement`] is
    /// nested); in the common case of a query narrower than 64 indices it's
    /// a single iteration. Each iteration is an array read plus a mask and
    /// compare, all against a `const`-evaluated `ROOT_MASK`, so this is
    /// effectively constant-time work, not proportional to the number of
    /// ranges combined to build `Self`.
    fn contains(start: usize, end: usize) -> bool {
        debug_assert!(start < end);
        let first_word = start / 64;
        let last_word = (end - 1) / 64;
        for word in first_word..=last_word {
            let first_bit = if word == first_word { start % 64 } else { 0 };
            let end_bit = if word == last_word { (end - 1) % 64 + 1 } else { 64 };
            let lower = u64::MAX << first_bit;
            let upper = if end_bit == 64 { u64::MAX } else { (1u64 << end_bit) - 1 };
            let required = lower & upper;
            if Self::ROOT_MASK[word] & required != required {
                return false;
            }
        }
        true
    }
}

/// Root entries in the non-empty half-open interval `START..END`.
///
/// ```compile_fail,E0080
/// use paging::structs::{CoveredRange, OwnedIndices};
///
/// const INVALID: () = <CoveredRange<2, 2> as OwnedIndices>::ASSERT_VALID;
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct CoveredRange<const START: usize, const END: usize>;

/// The union of two disjoint covered ranges.
///
/// ```compile_fail,E0080
/// use paging::structs::{CoveredRange, OwnedIndices, RootUnion};
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
///
/// This policy carries no lifetime: whether a page shared into this policy's
/// *borrowed* (non-owned) entries may still be freed is checked at runtime by
/// [`PagingAllocator::share_count`], not by the borrow checker (see
/// [`PageTable::new_from_sharing_top`] and [`PageTable::populate_shared`]),
/// unless [`MayFreePageTablePages::frees_shared`] is `false` for this
/// policy, in which case that tracking is skipped entirely. See
/// [`PagingOwnershipPolicy::MAY_SHARE_SUBTREE`] and
/// [`PagingOwnershipPolicy::MAY_FREE_PAGE_TABLE_PAGES`] for what the two
/// const parameters mean.
///
/// [`PageTable::new_from_sharing_top`]: crate::pagetable::PageTable::new_from_sharing_top
/// [`PageTable::populate_shared`]: crate::pagetable::PageTable::populate_shared
/// [`PagingAllocator::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
#[derive(Debug)]
pub struct Policy<
    Owned: OwnedIndices,
    const MAY_SHARE_SUBTREE: bool = false,
    // Packed `MayFreePageTablePages` bits; stable Rust cannot yet use that
    // enum directly as a const generic parameter (see `Self::from_bits`).
    const FREE_BITS: u8 = { MayFreePageTablePages::All as u8 },
> {
    owned: PhantomData<Owned>,
}

impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8> Clone
    for Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8> Copy
    for Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
}

impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8> Default
    for Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
    fn default() -> Self {
        Self::new()
    }
}

/// A kernel root-ownership policy. It owns every entry, so it never borrows
/// from another table. Defaults to shareable, tracked sharing (may be shared
/// from, and its top-level pages may be freed while shared, so real
/// [`PagingAllocator::share_count`] tracking applies).
///
/// [`PagingAllocator::share_count`]: crate::structs::os_contract::PagingAllocator::share_count
pub type KernelPolicy<Owned = AllRootEntries> =
    Policy<Owned, true, { MayFreePageTablePages::All as u8 }>;

/// A user root-ownership policy that may borrow some of its entries from the
/// table (or lock-protected table) it was shared from. Defaults to not being
/// shareable further, with tracked sharing on the entries it borrows (must
/// match whatever its source declared; see
/// [`PagingOwnershipPolicy::MAY_FREE_PAGE_TABLE_PAGES`]). Pass a
/// [`MayFreePageTablePages`] variant cast to `u8`, e.g.
/// `UserPolicy<Owned, { MayFreePageTablePages::Shared as u8 }>`.
pub type UserPolicy<Owned, const FREE_BITS: u8 = { MayFreePageTablePages::All as u8 }> =
    Policy<Owned, false, FREE_BITS>;

/// Compile-time gate: implemented only for policies whose
/// [`PagingOwnershipPolicy::MAY_SHARE_SUBTREE`] is `true`, so
/// [`PageTable::new_from_sharing_top`] and [`PageTable::populate_shared`]
/// reject any other source policy at the call site, rather than allowing it
/// silently.
///
/// What we would really like to write is a bound directly on the
/// associated const, e.g. `SourceOwned: PagingOwnershipPolicy<MAY_SHARE_SUBTREE
/// = true>`, but associated-const equality bounds are still unstable/
/// incomplete on this toolchain (`error[E0658]: associated const equality is
/// incomplete`, requires `#![feature(min_generic_const_args)]`; see
/// rust-lang/rust#132980). This marker trait is the stable workaround: it is
/// implemented only for `Policy<Owned, true, FREE_BITS>`, so bounding a
/// generic parameter by `MayShareSubtree` encodes "`MAY_SHARE_SUBTREE ==
/// true`" using only stable trait-bound machinery.
///
/// [`PageTable::new_from_sharing_top`]: crate::pagetable::PageTable::new_from_sharing_top
/// [`PageTable::populate_shared`]: crate::pagetable::PageTable::populate_shared
pub trait MayShareSubtree: PagingOwnershipPolicy {}

impl<Owned: OwnedIndices, const FREE_BITS: u8> MayShareSubtree for Policy<Owned, true, FREE_BITS> {}

impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8>
    Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
    pub(crate) fn new() -> Self {
        let () = Owned::ASSERT_VALID;
        Self { owned: PhantomData }
    }

    /// Returns whether this policy borrows the root entry from its kernel owner.
    pub fn borrows_top_entry(&self, index: usize) -> bool {
        assert!(index < PT_ENTRY_COUNT);
        !Owned::contains(index, index + 1)
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
            Owned::contains(first_index, end_index)
        } else {
            Owned::contains(first_index, PT_ENTRY_COUNT) && Owned::contains(0, end_index)
        }
    }
}

impl sealed::Sealed for NoRootEntries {}
impl sealed::Sealed for AllRootEntries {}
impl<const START: usize, const END: usize> sealed::Sealed for CoveredRange<START, END> {}
impl<Left: OwnedIndices, Right: OwnedIndices> sealed::Sealed for RootUnion<Left, Right> {}
impl<Set: OwnedIndices> sealed::Sealed for RootComplement<Set> {}
impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8> sealed::Sealed
    for Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
}

impl OwnedIndices for NoRootEntries {
    const ASSERT_VALID: () = ();
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = [0; PT_ENTRY_COUNT / 64];
}

impl OwnedIndices for AllRootEntries {
    const ASSERT_VALID: () = ();
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = [u64::MAX; PT_ENTRY_COUNT / 64];

    #[inline(always)]
    fn contains(start: usize, end: usize) -> bool {
        debug_assert!(start < end);
        assert!(end <= PT_ENTRY_COUNT);
        true
    }
}

impl<const START: usize, const END: usize> OwnedIndices for CoveredRange<START, END> {
    const ASSERT_VALID: () = {
        assert!(START < END);
        assert!(END <= PT_ENTRY_COUNT);
    };
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = root_mask(START, END);

    fn contains(start: usize, end: usize) -> bool {
        start >= START && end <= END
    }
}

impl<Left: OwnedIndices, Right: OwnedIndices> OwnedIndices for RootUnion<Left, Right> {
    const ASSERT_VALID: () = {
        let () = CoveragePair::<Left, Right>::ASSERT_DISJOINT;
    };
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = union_mask(Left::ROOT_MASK, Right::ROOT_MASK);

    // No cheap override: a queried range can straddle the `Left`/`Right`
    // boundary, owned partly by each side, so neither
    // `Left::contains(start, end)` nor `Right::contains(start, end)` alone
    // would report it (that pattern only asks "does one side own the whole
    // range", not "does the union, combined, own the whole range"). Fall
    // back to the trait's general `ROOT_MASK`-based check.
}

impl<Set: OwnedIndices> OwnedIndices for RootComplement<Set> {
    const ASSERT_VALID: () = Set::ASSERT_VALID;
    const ROOT_MASK: [u64; PT_ENTRY_COUNT / 64] = complement_mask(Set::ROOT_MASK);

    // No cheap override: `!Set::contains(start, end)` means "at least one
    // index in the range is missing from `Set`", not "every index in the
    // range is missing from `Set`" (the latter is what containment in the
    // complement actually requires). Fall back to the trait's general
    // `ROOT_MASK`-based check.
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
/// use paging::structs::{CoveredRange, KernelPolicy, compile_check_disjoint_policies};
///
/// type Left = KernelPolicy<CoveredRange<1, 4>>;
/// type Right = KernelPolicy<CoveredRange<3, 6>>;
///
/// const INVALID: () = compile_check_disjoint_policies::<Left, Right>();
/// ```
pub const fn compile_check_disjoint_policies<Left, Right>()
where
    Left: PagingOwnershipPolicy,
    Right: PagingOwnershipPolicy,
{
    let () = CoveragePair::<Left::Owned, Right::Owned>::ASSERT_DISJOINT;
}

pub(crate) fn compile_check_borrowed_disjoint_from<Source, Owned>(_source: &Source)
where
    Source: PagingOwnershipPolicy,
    Owned: OwnedIndices,
{
    let () = BorrowedCoveragePair::<Source::Owned, Owned>::ASSERT_DISJOINT;
}

/// Asserts at compile time (via an inline `const` block at the call site)
/// that a derived table's policy will decrement the same borrowed entries
/// its sharing source could increment: `Target`'s
/// [`MayFreePageTablePages::frees_shared`] must agree with `Source`'s
/// [`MayFreePageTablePages::frees_owned`]. Called from
/// [`PageTable::new_from_sharing_top`] and [`PageTable::populate_shared`] so
/// [`PTPageTree`]'s `Drop` can later read only its own policy's value and
/// still make the same share-count tracking decision the constructor made.
///
/// [`PageTable::new_from_sharing_top`]: crate::pagetable::PageTable::new_from_sharing_top
/// [`PageTable::populate_shared`]: crate::pagetable::PageTable::populate_shared
/// [`PTPageTree`]: crate::structs::ptpage::PTPageTree
pub const fn compile_check_matching_free_policy<Target, Source>()
where
    Target: PagingOwnershipPolicy,
    Source: PagingOwnershipPolicy,
{
    assert!(
        Target::MAY_FREE_PAGE_TABLE_PAGES.frees_shared()
            == Source::MAY_FREE_PAGE_TABLE_PAGES.frees_owned(),
        "a derived table's MAY_FREE_PAGE_TABLE_PAGES.frees_shared() must match its source's \
         MAY_FREE_PAGE_TABLE_PAGES.frees_owned(), so Drop can later make the same share-count \
         tracking decision from its own policy alone"
    );
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

impl<Owned: OwnedIndices, const MAY_SHARE_SUBTREE: bool, const FREE_BITS: u8> PagingOwnershipPolicy
    for Policy<Owned, MAY_SHARE_SUBTREE, FREE_BITS>
{
    type Owned = Owned;
    const MAY_SHARE_SUBTREE: bool = MAY_SHARE_SUBTREE;
    const MAY_FREE_PAGE_TABLE_PAGES: MayFreePageTablePages =
        MayFreePageTablePages::from_bits(FREE_BITS);

    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError> {
        let index = entry_index(address, root);
        if Owned::contains(index, index + 1) {
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
        Owned::contains(index, index + 1)
    }
}

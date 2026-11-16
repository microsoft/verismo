//! Ensures ownership ranges respect root indexes and canonical boundaries.
use paging::{
    address::VirtAddr,
    structs::{
        CoveredRange, PageLevel, PagingError, PagingOwnershipPolicy, RootComplement, RootUnion,
        UserPolicy, PT_ENTRY_COUNT,
    },
};

const PAGE: usize = 4096;

#[test]
fn exclusive_canonical_boundary_does_not_include_the_kernel_half() {
    fn check<const START: usize, const END: usize>(root: PageLevel) {
        let low = VirtAddr::from((1usize << 47) - PAGE);
        let high = VirtAddr::from(1usize << 47);
        let policy = UserPolicy::<RootComplement<CoveredRange<START, END>>>::default();
        assert_eq!(policy.check_range(root, low, high), Ok(()));
        assert_eq!(policy.check_range(root, high, high), Ok(()));
        assert_eq!(policy.check_address(root, high), Err(PagingError::PermissionDenied));
        assert_eq!(policy.check_range(root, low, high + PAGE), Err(PagingError::PermissionDenied));
    }
    check::<256, 512>(PageLevel::Level3);
    check::<511, 512>(PageLevel::Level4);
}

#[test]
fn ranges_cannot_hide_protected_indexes_by_wrapping_a_small_root() {
    let root = PageLevel::Level0;
    let size = root.size();
    let span = PT_ENTRY_COUNT * size;
    let policy = UserPolicy::<RootComplement<CoveredRange<1, 2>>>::default();
    assert_eq!(
        policy.check_range(root, VirtAddr::from(0usize), VirtAddr::from(span)),
        Err(PagingError::PermissionDenied)
    );
    assert_eq!(
        policy.check_range(root, VirtAddr::from(span - size), VirtAddr::from(span + size)),
        Ok(())
    );
    assert_eq!(
        policy.check_range(root, VirtAddr::from(span - size), VirtAddr::from(span + 2 * size)),
        Err(PagingError::PermissionDenied)
    );
}

#[test]
fn adjacent_policy_ranges_cover_their_shared_boundary() {
    type Adjacent = RootUnion<CoveredRange<0, 2>, CoveredRange<2, 4>>;
    let root = PageLevel::Level3;
    let start = VirtAddr::from(root.size());
    let end = VirtAddr::from(3 * root.size());
    assert_eq!(UserPolicy::<Adjacent>::default().check_range(root, start, end), Ok(()));
    assert_eq!(
        UserPolicy::<RootComplement<Adjacent>>::default().check_range(root, start, end),
        Err(PagingError::PermissionDenied)
    );
}

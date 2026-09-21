use super::*;

#[test]
fn exclusive_canonical_boundary_does_not_include_the_kernel_half() {
    fn check<const START: usize, const END: usize>(root: PageLevel) {
        let low = VirtAddr::from(LOW_CANONICAL_END - 4096);
        let high = VirtAddr::from(LOW_CANONICAL_END);
        let policy = UserPolicy::<RootRange<START, END>>::new();
        assert_eq!(policy.check_range(root, low, high), Ok(()));
        assert_eq!(policy.check_range(root, high, high), Ok(()));
        assert_eq!(policy.check_address(root, high), Err(PagingError::PermissionDenied));
        assert_eq!(policy.check_range(root, low, high + 4096), Err(PagingError::PermissionDenied));
    }
    check::<256, 512>(PageLevel::Level3);
    check::<511, 512>(PageLevel::Level4);
}

#[test]
fn ranges_cannot_hide_protected_indexes_by_wrapping_a_small_root() {
    let root = PageLevel::Level0;
    let size = root.size();
    let span = PT_ENTRY_COUNT * size;
    let policy = UserPolicy::<RootRange<1, 2>>::new();
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
fn every_reserved_entry_is_immutable_and_non_owned() {
    let policy = UserPolicy::<RootRange<1, 3>>::new();
    assert!(policy.owns_top_entry(0));
    assert!(!policy.owns_top_entry(1));
    assert!(!policy.owns_top_entry(2));
    assert!(policy.owns_top_entry(3));
    for index in 1..3 {
        assert_eq!(
            policy
                .check_address(PageLevel::Level3, VirtAddr::from(index * PageLevel::Level3.size())),
            Err(PagingError::PermissionDenied)
        );
    }
}

#[test]
fn empty_reserved_set_allows_every_entry() {
    let policy = UserPolicy::<RootRange<256, 256>>::new();
    for index in 0..PT_ENTRY_COUNT {
        assert!(policy.owns_top_entry(index));
        assert_eq!(
            policy
                .check_address(PageLevel::Level3, VirtAddr::from(index * PageLevel::Level3.size())),
            Ok(())
        );
    }
    assert_eq!(
        policy.check_range(PageLevel::Level0, VirtAddr::from(0usize), VirtAddr::from(1usize << 30)),
        Ok(())
    );
}

#[test]
fn unions_protect_each_disjoint_range_and_own_the_gaps() {
    type Reserved = RootUnion<RootRange<1, 3>, RootRange<7, 9>>;
    let policy = UserPolicy::<Reserved>::new();
    for index in [1, 2, 7, 8] {
        assert!(policy.borrows_top_entry(index));
        assert!(!policy.owns_top_entry(index));
    }
    for index in [0, 3, 6, 9] {
        assert!(!policy.borrows_top_entry(index));
        assert!(policy.owns_top_entry(index));
    }
    let root = PageLevel::Level3;
    let address = |index| VirtAddr::from(index * root.size());
    assert_eq!(
        policy.check_range(root, address(2), address(8)),
        Err(PagingError::PermissionDenied)
    );
    assert_eq!(policy.check_range(root, address(3), address(7)), Ok(()));
}

#[test]
#[should_panic]
fn reversed_bounds_are_rejected() {
    let _ = UserPolicy::<RootRange<2, 1>>::new();
}

#[test]
#[should_panic]
fn bounds_past_the_root_are_rejected() {
    let _ = UserPolicy::<RootRange<0, { PT_ENTRY_COUNT + 1 }>>::new();
}

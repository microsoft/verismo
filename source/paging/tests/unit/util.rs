use super::*;

#[test]
fn test_mem_utils() {
    // Align up
    assert_eq!(align_up(7, 4), 8);
    assert_eq!(align_up(15, 8), 16);
    assert_eq!(align_up(10, 2), 10);
    // Align down
    assert_eq!(align_down(7, 4), 4);
    assert_eq!(align_down(15, 8), 8);
    assert_eq!(align_down(10, 2), 10);
    // Page align up
    assert_eq!(page_align_up(4096), 4096);
    assert_eq!(page_align_up(4097), 8192);
    assert_eq!(page_align_up(0), 0);
    // Page offset
    assert_eq!(page_offset(4096), 0);
    assert_eq!(page_offset(4097), 1);
    assert_eq!(page_offset(0), 0);
    // Overlaps
    assert!(overlap(1, 5, 3, 6));
    assert!(overlap(0, 10, 5, 15));
    assert!(!overlap(1, 5, 6, 8));
}

//! Ensures page ranges stop at address boundaries and skip the canonical gap.
use paging::{
    address::VirtAddr,
    structs::Page,
};

#[test]
fn inclusive_page_range_stops_at_the_last_addressable_page() {
    let page: Page = Page::containing_address(VirtAddr::from(usize::MAX));
    let mut range = Page::range_inclusive(page, page);

    assert_eq!(range.next().map(Page::start_address), Some(page.start_address()));
    assert!(range.next().is_none());
}

#[test]
fn page_range_length_skips_the_noncanonical_address_gap() {
    let low: Page =
        Page::from_start_address(VirtAddr::from(0x0000_7fff_ffff_f000usize)).unwrap();
    let high: Page =
        Page::from_start_address(VirtAddr::from(0xffff_8000_0000_0000usize)).unwrap();
    let range = Page::range_inclusive(low, high);

    assert_eq!(range.len(), 2);
    assert_eq!(range.count(), 2);
}

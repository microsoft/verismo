//! Shared page-table types, sizes, ownership policies, and platform contracts.
pub(crate) mod address;
pub(crate) mod arch_contract;
pub(crate) mod entry;
pub(crate) mod frame;
pub(crate) mod level;
pub(crate) mod os_contract;
pub(crate) mod page;
pub(crate) mod sizes;
pub(crate) mod tlb;

pub use arch_contract::{ArchPagingMeta, GenericPageTableFlags};
pub use entry::PTEntry;
pub use frame::{PfnNotValid, PhysFrame, PhysFrameRange, PhysFrameRangeInclusive};
pub use level::{InnerLevel, LevelSpec, Lvl, PageLevel};
pub use os_contract::{DirectMappedAllocator, MapRegionError, PagingAllocator, PagingError};
pub use page::{AddressNotAligned, Page, PageRange, PageRangeInclusive};
pub use sizes::{
    entry_index, entry_index_at, entry_index_bits, pt_entry_index_bits, Huge, PageOffset, PageSize,
    Regular, SizeLevel2, SizeLevel3, SizeLevel4, ENTRY_WIDTH, INDEX_MASK, PAGE_OFFSET_WIDTH,
    PAGE_SIZE, PAGE_TABLE_INDEX_WIDTH, PT_ENTRY_COUNT,
};

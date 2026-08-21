/// Support up to 5 levels of page tables.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(usize)]
pub enum PageLevel {
    Level0 = 0, // 4K
    Level1 = 1, // 2M
    Level2 = 2, // 1G
    Level3 = 3, // 512G
    Level4 = 4, // 256T
}

#[derive(Clone, Copy, Debug)]
pub struct PageTableEntry<A: ArchPagingMeta> {
    val: usize,
    dummy: core::marker::PhantomData<A>,
    level: Tracked<PageLevel>,
}

impl PageLevel {
    pub const fn page_count(&self) -> usize {
        match self {
            PageLevel::Level0 => 1,
            PageLevel::Level1 => PageLevel::Level0.page_count() * 512,
            PageLevel::Level2 => PageLevel::Level1.page_count() * 512,
            PageLevel::Level3 => PageLevel::Level2.page_count() * 512,
            PageLevel::Level4 => PageLevel::Level3.page_count() * 512,
        }
    }
}

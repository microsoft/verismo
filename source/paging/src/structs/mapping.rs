//! Handles on one entry of a live table. A mutable handle stages its edit in a
//! copy and commits it with a single atomic store, so a walker never sees a
//! half-written entry, and the commit is what produces the flush obligation.
use core::marker::PhantomData;

use crate::structs::address::VirtAddr;
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingError;
use crate::structs::ptpage::Mapping;
use crate::structs::tlb::MayNeedFlush;

/// A removed entry paired with any TLB invalidation it leaves outstanding.
pub type UnmapEntryResult<A> =
    Result<(Option<PTEntry<A>>, MayNeedFlush<<A as ArchPagingMeta>::TlbFlushTok>), PagingError>;

/// What a read handle offers.
pub trait MappingRefOps<'a, A: ArchPagingMeta>: Sized {
    /// The level the walk stopped at.
    fn level(&self) -> PageLevel;

    fn read(&self) -> PTEntry<A>;
}

/// What a mutable handle offers: the same reads, plus a staged edit and the
/// commit that installs it.
pub trait MappingMutOps<'a, A: ArchPagingMeta>: Sized {
    fn level(&self) -> PageLevel;

    fn read(&self) -> PTEntry<A>;

    /// The scratch entry the `do_*` helpers edit before it is committed.
    fn staged(&mut self) -> Mapping<'_, A>;

    /// Installs the staged entry and reports what it may have made stale.
    /// Present leaf/table transitions require an architecture-aware operation.
    fn commit(self) -> MayNeedFlush<A::TlbFlushTok>;

    /// Installs an entry that owes no flush, because the entry it replaces was
    /// not present. Fails without writing anything if one was.
    fn commit_no_flush<F, O>(self, update: F) -> Result<O, PagingError>
    where
        F: FnOnce(Mapping<'_, A>) -> Result<O, PagingError>;
}

/// A read handle on an entry of a live table.
#[derive(Debug)]
pub struct MappingRef<'a, A: ArchPagingMeta> {
    level: PageLevel,
    entry: PTEntryRef<'a, A>,
}

impl<'a, A: ArchPagingMeta> MappingRef<'a, A> {
    /// A handle on `entry`, which sits at `level`.
    ///
    /// # Safety
    /// `entry` must remain allocated and atomically accessible for all of `'a`, including
    /// initialized, writable storage and atomic access without ordinary entry references.
    pub unsafe fn new(level: PageLevel, entry: *const PTEntry<A>) -> Self {
        Self::from_view(level, unsafe { PTEntryRef::from_raw(entry.cast_mut()) })
    }

    pub(crate) fn from_view(level: PageLevel, entry: PTEntryRef<'a, A>) -> Self {
        Self { level, entry }
    }
}

impl<'a, A: ArchPagingMeta> MappingRefOps<'a, A> for MappingRef<'a, A> {
    fn level(&self) -> PageLevel {
        self.level
    }

    fn read(&self) -> PTEntry<A> {
        self.entry.load()
    }
}

/// A mutable handle on an entry of a live table.
#[derive(Debug)]
pub struct MappingMut<'a, A: ArchPagingMeta> {
    vaddr: Option<VirtAddr>,
    level: PageLevel,
    entry: PTEntryRef<'a, A>,
    original: Option<PTEntry<A>>,
    staged: Option<PTEntry<A>>,
    lifetime: PhantomData<&'a mut ()>,
}

impl<'a, A: ArchPagingMeta> MappingMut<'a, A> {
    /// A handle on `entry`, which sits at `level` and describes `vaddr`. With
    /// no address -- an edit above the walk, such as populating a subtree --
    /// the commit cannot name what went stale and asks for a full flush.
    ///
    /// # Safety
    /// `entry` must remain allocated and atomically accessible for all of `'a`, and other
    /// software writers must be excluded throughout this handle's lifetime.
    /// Every committed value must preserve the containing tree's level and
    /// ownership invariants. This handle cannot replace a present leaf with a
    /// table or a present table with a leaf. Commits preserve hardware A/D
    /// updates when the staged entry keeps the original leaf/table kind.
    pub unsafe fn new(vaddr: Option<VirtAddr>, level: PageLevel, entry: *mut PTEntry<A>) -> Self {
        Self::from_view(vaddr, level, unsafe { PTEntryRef::from_raw(entry) })
    }

    pub(crate) fn from_view(
        vaddr: Option<VirtAddr>,
        level: PageLevel,
        entry: PTEntryRef<'a, A>,
    ) -> Self {
        Self { vaddr, level, entry, original: None, staged: None, lifetime: PhantomData }
    }
}

impl<'a, A: ArchPagingMeta> MappingMutOps<'a, A> for MappingMut<'a, A> {
    fn level(&self) -> PageLevel {
        self.level
    }

    fn read(&self) -> PTEntry<A> {
        self.entry.load()
    }

    fn staged(&mut self) -> Mapping<'_, A> {
        if self.staged.is_none() {
            let original = self.entry.load();
            self.original = Some(original);
            self.staged = Some(original);
        }
        let staged = self.staged.as_mut().unwrap();
        Mapping::new(self.level, staged)
    }

    fn commit(self) -> MayNeedFlush<A::TlbFlushTok> {
        let Some(staged) = self.staged else {
            return MayNeedFlush::none();
        };
        let original = self.original.unwrap();
        assert!(
            !original.present()
                || !staged.present()
                || original.is_leaf(self.level) == staged.is_leaf(self.level),
            "present leaf/table transitions require architecture-aware publication"
        );
        let preserve_ad = original.present()
            && staged.present()
            && original.is_leaf(self.level) == staged.is_leaf(self.level);
        if preserve_ad {
            self.entry.update_preserving_ad(original, staged);
        } else {
            self.entry.store(staged);
        }
        match self.vaddr {
            Some(vaddr) => MayNeedFlush::new(vaddr, self.level),
            None => MayNeedFlush::all(),
        }
    }

    fn commit_no_flush<F, O>(mut self, update: F) -> Result<O, PagingError>
    where
        F: FnOnce(Mapping<'_, A>) -> Result<O, PagingError>,
    {
        let level = self.level;
        let staged = self.staged();
        if staged.entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        let ret = update(staged)?;
        let entry = *self.staged().entry;
        self.entry.store(entry);
        Ok(ret)
    }
}

/// A staged entry is itself a mutable handle, so the `do_*` helpers can be
/// driven either from a walk or from an edit already in progress. Committing
/// one owes nothing: the write went to the copy, not to the table.
impl<'a, A: ArchPagingMeta> MappingMutOps<'a, A> for Mapping<'a, A> {
    fn level(&self) -> PageLevel {
        self.level
    }

    fn read(&self) -> PTEntry<A> {
        *self.entry
    }

    fn staged(&mut self) -> Mapping<'_, A> {
        Mapping::new(self.level, self.entry)
    }

    fn commit(self) -> MayNeedFlush<A::TlbFlushTok> {
        MayNeedFlush::none()
    }

    fn commit_no_flush<F, O>(self, update: F) -> Result<O, PagingError>
    where
        F: FnOnce(Mapping<'_, A>) -> Result<O, PagingError>,
    {
        update(self)
    }
}

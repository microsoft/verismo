//! Handles on one entry of a live table. A mutable handle stages its edit in a
//! copy and commits it with a single volatile write, so a walker never sees a
//! half-written entry, and the commit is what produces the flush obligation.
use core::marker::PhantomData;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingError;
use crate::structs::ptpage::Mapping;
use crate::structs::tlb::MayNeedFlush;

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
    entry: *const PTEntry<A>,
    lifetime: PhantomData<&'a PTEntry<A>>,
}

impl<'a, A: ArchPagingMeta> MappingRef<'a, A> {
    /// A handle on `entry`, which sits at `level`.
    ///
    /// # Safety
    /// `entry` must point at an entry of a mapped table page that outlives `'a`.
    pub unsafe fn new(level: PageLevel, entry: *const PTEntry<A>) -> Self {
        Self { level, entry, lifetime: PhantomData }
    }
}

impl<'a, A: ArchPagingMeta> MappingRefOps<'a, A> for MappingRef<'a, A> {
    fn level(&self) -> PageLevel {
        self.level
    }

    fn read(&self) -> PTEntry<A> {
        // SAFETY: the constructor's caller vouched for the pointer, and `'a`
        // keeps the table alive.
        unsafe { PTEntry::read_pte(self.entry) }
    }
}

/// A mutable handle on an entry of a live table.
#[derive(Debug)]
pub struct MappingMut<'a, A: ArchPagingMeta> {
    vaddr: Option<VirtAddr>,
    level: PageLevel,
    entry: *mut PTEntry<A>,
    staged: Option<PTEntry<A>>,
    lifetime: PhantomData<&'a mut PTEntry<A>>,
}

impl<'a, A: ArchPagingMeta> MappingMut<'a, A> {
    /// A handle on `entry`, which sits at `level` and describes `vaddr`. With
    /// no address -- an edit above the walk, such as populating a subtree --
    /// the commit cannot name what went stale and asks for a full flush.
    ///
    /// # Safety
    /// `entry` must point at an entry of a mapped table page that outlives `'a`
    /// and that no other handle writes meanwhile.
    pub unsafe fn new(vaddr: Option<VirtAddr>, level: PageLevel, entry: *mut PTEntry<A>) -> Self {
        Self { vaddr, level, entry, staged: None, lifetime: PhantomData }
    }
}

impl<'a, A: ArchPagingMeta> MappingMutOps<'a, A> for MappingMut<'a, A> {
    fn level(&self) -> PageLevel {
        self.level
    }

    fn read(&self) -> PTEntry<A> {
        // SAFETY: as in `MappingRef::read`.
        unsafe { PTEntry::read_pte(self.entry) }
    }

    fn staged(&mut self) -> Mapping<'_, A> {
        let entry = self.entry;
        // SAFETY: as in `MappingRef::read`; the first stage seeds the copy from
        // the live entry.
        let staged = self.staged.get_or_insert_with(|| unsafe { PTEntry::read_pte(entry) });
        Mapping::new(self.level, staged)
    }

    fn commit(self) -> MayNeedFlush<A::TlbFlushTok> {
        let Some(staged) = self.staged else {
            return MayNeedFlush::none();
        };
        // SAFETY: as in `MappingRef::read`, and a word-sized store is what the
        // hardware needs to see the entry whole.
        unsafe { PTEntry::write_pte(self.entry, staged) };
        match self.vaddr {
            Some(vaddr) => MayNeedFlush::new(vaddr, self.level),
            None => MayNeedFlush::all(),
        }
    }

    fn commit_no_flush<F, O>(mut self, update: F) -> Result<O, PagingError>
    where
        F: FnOnce(Mapping<'_, A>) -> Result<O, PagingError>,
    {
        let (vaddr, level) = (self.vaddr, self.level);
        let staged = self.staged();
        if staged.entry.present() {
            let offset = vaddr.map_or(0, |v| v.bits() & (level.size() - 1));
            return Err(PagingError::EntryAlreadyPresent {
                frame: PhysAddr::from(staged.entry.address() + offset),
                level,
            });
        }
        let ret = update(staged)?;
        let entry = *self.staged().entry;
        // SAFETY: as in `commit`.
        unsafe { PTEntry::write_pte(self.entry, entry) };
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

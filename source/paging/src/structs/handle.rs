//! The handle a caller holds on a page table.
//!
//! Two levels of exclusion, following verios-pagetable: the operations that
//! only walk or grow the tree take `&self` and may run concurrently, while
//! reclaiming interior pages takes `&mut self`, because a walker must not be
//! standing in a page that is being freed. Rust's borrow checker is what
//! enforces the outer level, and the per-page host lock the inner one.
//!
//! Unlike verios-pagetable, whose handle holds no tokens and threads them
//! through every call, the tokens live in the handle: the reader half of a
//! table page is shareable by `&`, so `&PageTableHandle` is exactly the
//! capability a lock-free walk needs, and `&mut PageTableHandle` is exactly the
//! exclusion `free` needs.
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::host_contract::PagingHost;
use crate::structs::level::PagingLevel;
use crate::structs::table::{ChildOf, TableReaders};

verus! {

/// A page table rooted at level `L`, owned by the holder of this handle.
///
/// The root page is adopted, never allocated here: whoever installs a table in
/// hardware owns its lifetime, and this handle owns only the right to read and
/// update its slots.
pub struct PageTableHandle<A: ArchPagingMeta, H: PagingHost, L: PagingLevel + ChildOf<A, H>> {
    root: VirtAddr,
    readers: Tracked<TableReaders<A, H, L>>,
    deposit: Tracked<H::Deposit>,
    dummy: PhantomData<(A, H, L)>,
}

impl<A: ArchPagingMeta, H: PagingHost, L: PagingLevel + ChildOf<A, H>> PageTableHandle<A, H, L> {
    pub closed spec fn root_spec(&self) -> VirtAddr {
        self.root
    }

    pub closed spec fn readers_spec(&self) -> TableReaders<A, H, L> {
        self.readers@
    }

    pub closed spec fn deposit_spec(&self) -> H::Deposit {
        self.deposit@
    }

    /// The tokens describe the root page, and the host receipt names the lock
    /// that guards it.
    pub open spec fn inv(&self) -> bool {
        &&& self.readers_spec().wf()
        &&& self.readers_spec().base == self.root_spec()@
        &&& H::deposit_page(self.deposit_spec()) == self.root_spec()@
        &&& H::deposit_slot_ids(self.deposit_spec()) == self.readers_spec().ids
    }

    #[verifier::when_used_as_spec(root_spec)]
    pub fn root(&self) -> (ret: VirtAddr)
        returns
            self.root_spec(),
    {
        self.root
    }

    /// Adopts a root page whose slots the caller already owns.
    pub fn new(
        root: VirtAddr,
        Tracked(readers): Tracked<TableReaders<A, H, L>>,
        Tracked(deposit): Tracked<H::Deposit>,
    ) -> (ret: Self)
        requires
            readers.wf(),
            readers.base == root@,
            H::deposit_page(deposit) == root@,
            H::deposit_slot_ids(deposit) == readers.ids,
        ensures
            ret.inv(),
            ret.root_spec() == root,
            ret.readers_spec() == readers,
            ret.deposit_spec() == deposit,
    {
        PageTableHandle {
            root,
            readers: Tracked(readers),
            deposit: Tracked(deposit),
            dummy: PhantomData,
        }
    }

    /// The root tokens, as a walk needs them: shared, so several walks may hold
    /// them at once.
    pub fn borrow_readers(&self) -> (ret: Tracked<&TableReaders<A, H, L>>)
        ensures
            *ret@ == self.readers_spec(),
    {
        Tracked(self.readers.borrow())
    }

    pub fn borrow_deposit(&self) -> (ret: Tracked<&H::Deposit>)
        ensures
            *ret@ == self.deposit_spec(),
    {
        Tracked(self.deposit.borrow())
    }

    /// Gives the root tokens back, dissolving the handle.
    pub fn into_parts(self) -> (ret: (VirtAddr, Tracked<TableReaders<A, H, L>>, Tracked<
        H::Deposit,
    >))
        ensures
            ret.0 == self.root_spec(),
            ret.1@ == self.readers_spec(),
            ret.2@ == self.deposit_spec(),
    {
        (self.root, self.readers, self.deposit)
    }
}

} // verus!

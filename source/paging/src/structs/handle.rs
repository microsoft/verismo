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
use crate::structs::level::PagingLevel;
use crate::structs::host_contract::PagingHost;
use crate::structs::concurrent_pt::PTPageSharedPerm;

verus! {

/// A page table rooted at the architecture's top level, owned by the holder of
/// this handle.
///
/// The root page is adopted, never allocated here: whoever installs a table in
/// hardware owns its lifetime, and this handle owns only the right to read and
/// update its slots.
pub struct PageTableHandle<A: ArchPagingMeta, H: PagingHost> {
    root: VirtAddr,
    page: Tracked<PTPageSharedPerm<A>>,
    deposit: Tracked<H::Deposit>,
    dummy: PhantomData<(A, H)>,
}

impl<A: ArchPagingMeta, H: PagingHost> PageTableHandle<A, H> {
    pub closed spec fn root_spec(&self) -> VirtAddr {
        self.root
    }

    pub closed spec fn page_spec(&self) -> PTPageSharedPerm<A> {
        self.page@
    }

    pub closed spec fn deposit_spec(&self) -> H::Deposit {
        self.deposit@
    }

    /// The tokens describe the root page, and the host receipt names the lock
    /// that guards it.
    pub open spec fn inv(&self) -> bool {
        &&& self.page_spec().wf()
        &&& self.page_spec().base == self.root_spec()@
        &&& self.page_spec().depth == A::RootLevel::DEPTH
        &&& H::deposit_page(self.deposit_spec()) == self.root_spec()@
        &&& H::deposit_slot_ids(self.deposit_spec()) =~= self.page_spec().ids()
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
        Tracked(page): Tracked<PTPageSharedPerm<A>>,
        Tracked(deposit): Tracked<H::Deposit>,
    ) -> (ret: Self)
        requires
            page.wf(),
            page.base == root@,
            page.depth == A::RootLevel::DEPTH,
            H::deposit_page(deposit) == root@,
            H::deposit_slot_ids(deposit) =~= page.ids(),
        ensures
            ret.inv(),
            ret.root_spec() == root,
            ret.page_spec() == page,
            ret.deposit_spec() == deposit,
    {
        PageTableHandle { root, page: Tracked(page), deposit: Tracked(deposit), dummy: PhantomData }
    }

    /// The root tokens, as a walk needs them: shared, so several walks may hold
    /// them at once.
    pub fn borrow_page(&self) -> (ret: Tracked<&PTPageSharedPerm<A>>)
        ensures
            *ret@ == self.page_spec(),
    {
        Tracked(self.page.borrow())
    }

    pub fn borrow_deposit(&self) -> (ret: Tracked<&H::Deposit>)
        ensures
            *ret@ == self.deposit_spec(),
    {
        Tracked(self.deposit.borrow())
    }

    /// Gives the root tokens back, dissolving the handle.
    pub fn into_parts(self) -> (ret: (VirtAddr, Tracked<PTPageSharedPerm<A>>, Tracked<H::Deposit>))
        ensures
            ret.0 == self.root_spec(),
            ret.1@ == self.page_spec(),
            ret.2@ == self.deposit_spec(),
    {
        (self.root, self.page, self.deposit)
    }
}

} // verus!

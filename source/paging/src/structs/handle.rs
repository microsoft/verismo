//! The handle a caller holds on a page table.
//!
//! Two levels of exclusion. The operations that only walk or grow the tree take
//! `&self` and may run concurrently; reclaiming interior pages takes `&mut
//! self`, because a walker must not be standing in a page that is being freed.
//! Rust's borrow checker enforces the outer level and the OS's per-page lock
//! the inner one -- see `os_contract`.
//!
//! The tokens live in the handle rather than being threaded through every call:
//! the reader half of a table page is shareable by `&`, so `&PageTableHandle`
//! is exactly the capability a lock-free walk needs, and `&mut
//! PageTableHandle` is exactly the exclusion `free` needs.
use core::marker::PhantomData;

use vstd::prelude::*;

use crate::structs::address::{Address, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::concurrent_pt::PTPageSharedPerm;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingHandler;
use crate::structs::state::PTInstallState;

verus! {

/// A page table rooted at the architecture's top level, owned by the holder of
/// this handle.
///
/// The root page is adopted, never allocated here: whoever installs a table in
/// hardware owns its lifetime, and this handle owns only the right to read and
/// update its slots.
pub struct PageTableHandle<A: ArchPagingMeta, H: PagingHandler> {
    root: VirtAddr,
    page: Tracked<PTPageSharedPerm<A>>,
    install: Tracked<PTInstallState<A>>,
    dummy: PhantomData<(A, H)>,
}

impl<A: ArchPagingMeta, H: PagingHandler> PageTableHandle<A, H> {
    pub closed spec fn root_spec(&self) -> VirtAddr {
        self.root
    }

    pub closed spec fn page_spec(&self) -> PTPageSharedPerm<A> {
        self.page@
    }

    pub closed spec fn install_spec(&self) -> PTInstallState<A> {
        self.install@
    }

    /// The level of the root page, and so how deep the tree is. Nothing static
    /// fixes it: an operation that also holds the register state checks it
    /// against `PagingRegisters::level_count`.
    pub open spec fn root_level(&self) -> PageLevel {
        self.page_spec().level
    }

    /// Whether the hardware may be walking this tree.
    pub open spec fn installed(&self) -> bool {
        self.install_spec().installed()
    }

    /// The tokens describe the root page, and the OS's lock for that address
    /// guards its writers.
    pub open spec fn inv(&self) -> bool {
        &&& self.page_spec().wf()
        &&& self.page_spec().base == self.root_spec()@
        &&& self.install_spec().root_frame() == H::spec_vaddr_to_paddr(self.root_spec()@)
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
        Tracked(install): Tracked<PTInstallState<A>>,
    ) -> (ret: Self)
        requires
            page.wf(),
            page.base == root@,
            install.root_frame() == H::spec_vaddr_to_paddr(root@),
        ensures
            ret.inv(),
            ret.root_spec() == root,
            ret.page_spec() == page,
            ret.install_spec() == install,
    {
        PageTableHandle { root, page: Tracked(page), install: Tracked(install), dummy: PhantomData }
    }

    /// The root tokens, as a walk needs them: shared, so several walks may hold
    /// them at once.
    pub fn borrow_page(&self) -> (ret: Tracked<&PTPageSharedPerm<A>>)
        ensures
            *ret@ == self.page_spec(),
    {
        Tracked(self.page.borrow())
    }

    /// Gives the root tokens back, dissolving the handle.
    pub fn into_parts(self) -> (ret: (
        VirtAddr,
        Tracked<PTPageSharedPerm<A>>,
        Tracked<PTInstallState<A>>,
    ))
        ensures
            ret.0 == self.root_spec(),
            ret.1@ == self.page_spec(),
            ret.2@ == self.install_spec(),
    {
        (self.root, self.page, self.install)
    }
}

} // verus!

//! What an embedder owes the page table.
//!
//! The page table allocates no memory, takes no lock and knows no virtual
//! memory layout of its own: each of those is a service the OS supplies, and
//! this file is where the corresponding proof obligations are concentrated.
//! One verified page table can then be embedded in several systems, each
//! discharging these obligations in its own verification, which is the same
//! shape as the register contract in `arch::x86_64::reg_contract`.
//!
//! # Two levels of exclusion
//!
//! Concurrency here is finer than one lock per table. The *outer* level guards
//! the shape of the tree -- which pages are linked into it -- and is what an
//! operation that reclaims interior pages needs; the crate expresses it as
//! `&mut` on the handle, so an OS that shares a table between threads puts its
//! own reader/writer lock around the handle and gets the outer level from
//! Rust. The *inner* level is one lock per table page, guarding that page's
//! entries, and it is the only lock a map or an unmap takes: two threads
//! updating different pages never contend. That inner lock is [`PageLock`],
//! and the OS supplies it, because only the OS knows where to keep a lock for
//! a frame it allocated.
//!
//! A walk takes neither lock. It reads slots through `concurrent_rw`, which is
//! what makes a reader's view of a slot imprecise but never wrong.
use concurrent_rw::RWShared;
use vstd::prelude::*;
use vstd::raw_ptr::{IsExposed, PointsTo};

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{slot_addr, ArchPagingMeta};
use crate::structs::concurrent_pt::{PTPageSharedPerm, PTPageWritePerm};
use crate::structs::entry::PTEntry;
use crate::structs::ptpage::PTPage;

verus! {

/// Why an operation could not be carried out.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum PagingError {
    /// No frame was available for an intermediate table.
    AllocFrame,
    /// The walk found no mapping for the address.
    NotMapped,
    /// A mapping is already installed where one was asked for.
    EntryAlreadyPresent,
    /// The tree is not deep enough for the requested page size.
    InvalidLevel,
    /// A table pointer sits where a mapping was expected. Overwriting one
    /// would strand the subtree below it, so no operation on a leaf will.
    NotLeafEntry,
}

/// A freshly allocated table page, before it becomes part of any tree.
///
/// The allocator hands over the raw ownership of the frame's words; the page
/// table turns them into the reader and writer tokens of a page. Keeping this
/// as a type of its own is what stops a caller from presenting one frame
/// twice: the tokens are linear.
pub tracked struct PTPageInit<A: ArchPagingMeta> {
    pub ghost base: usize,
    pub tracked provenance: IsExposed,
    pub tracked slots: Seq<PointsTo<usize>>,
    pub ghost arch: core::marker::PhantomData<A>,
}

impl<A: ArchPagingMeta> PTPageInit<A> {
    /// Every word of the frame is owned and lies where the architecture puts
    /// the entry of that index.
    ///
    /// This is what returning a frame needs: a page being given back holds
    /// whatever was last written to it, and the allocator is the one that
    /// decides whether to zero it.
    pub open spec fn wf_owned(self) -> bool {
        &&& self.slots.len() == PTEntry::<A>::count_per_page()
        &&& forall|index: int|
            0 <= index < self.slots.len() ==> {
                &&& (#[trigger] self.slots[index]).ptr()@.addr == slot_addr::<A>(self.base, index)
                &&& self.slots[index].ptr()@.provenance == self.provenance@
                &&& self.slots[index].is_init()
            }
    }

    /// [`Self::wf_owned`], and zeroed: what a page has to be before it can
    /// become a table page, since every slot starts out empty.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_owned()
        &&& forall|index: int|
            0 <= index < self.slots.len() ==> (#[trigger] self.slots[index]).value() == 0usize
    }
}

/// The lock guarding one table page's entries.
///
/// The page table never sees the lock's implementation, only the writer tokens
/// it hands out: holding [`PTPageWritePerm`] *is* what makes an update the only
/// writer of those slots, and this trait is the promise that the OS gives them
/// to one thread at a time.
///
/// A lock is addressed by the page it guards, and every method names the page's
/// reader tokens as well. That pairing is the whole obligation: the OS promises
/// that the writers it hands out for the page mapped at `page()` are the writer
/// halves of *those* readers, so a thread that walked to a page and then locked
/// it may write the slots it walked through. The page table cannot establish
/// that itself -- it is the OS that allocated the frame, split its ownership,
/// and kept the writers.
pub trait PageLock: Sized + 'static {
    /// The page this lock guards, as a virtual address.
    spec fn page(&self) -> usize;

    /// Takes the lock and hands back the writer half of the page's slots.
    fn lock<A: ArchPagingMeta>(&self, Tracked(page): Tracked<&PTPageSharedPerm<A>>) -> (ret:
        Tracked<PTPageWritePerm<A>>)
        requires
            page.wf(),
            page.base == self.page(),
        ensures
            ret@.ids() =~= page.ids(),
        opens_invariants none
    ;

    /// Returns the writer half and releases the lock.
    fn unlock<A: ArchPagingMeta>(
        &self,
        Tracked(page): Tracked<&PTPageSharedPerm<A>>,
        Tracked(writers): Tracked<PTPageWritePerm<A>>,
    )
        requires
            page.base == self.page(),
            writers.ids() =~= page.ids(),
        opens_invariants none
    ;

    /// Puts a freshly built page's writers into the lock's custody.
    ///
    /// This is the last step of publishing a page: after it, the page is
    /// reachable by other walkers, and its writers are reachable only through
    /// this lock.
    fn deposit<A: ArchPagingMeta>(
        &self,
        Tracked(page): Tracked<&PTPageSharedPerm<A>>,
        Tracked(writers): Tracked<PTPageWritePerm<A>>,
    )
        requires
            page.base == self.page(),
            writers.ids() =~= page.ids(),
        opens_invariants none
    ;
}

/// OS-level page table services: address translation, frame management, and
/// where each frame's lock lives.
///
/// Every method is an associated function: the implementing type is a marker
/// that is never instantiated.
pub trait OSPagingContract<A: ArchPagingMeta>: 'static + Sized {
    /// The lock the OS keeps for each table page. One type serves every page;
    /// [`Self::page_lock`] says which lock belongs to which page.
    type PageLock: PageLock;

    spec fn spec_vaddr_to_paddr(vaddr: usize) -> usize;

    /// Where the OS has mapped a page-table frame. `paddr` is always clean --
    /// callers strip the architecture's confidentiality tags first.
    ///
    fn paddr_to_vaddr(paddr: PhysAddr) -> (ret: VirtAddr)
        ensures
            ret@ == A::spec_paddr_to_vaddr(paddr@),
    ;

    /// The frame a table page occupies, given a pointer to the page.
    fn page_paddr(page: *mut PTPage<A>) -> (ret: PhysAddr)
        ensures
            ret@ == Self::spec_vaddr_to_paddr(page@.addr),
    ;

    /// Allocates a zeroed frame for a table page and gives up the ownership of
    /// its words.
    ///
    /// The address returned is *clean*: no confidentiality or shared tag is
    /// set, and callers apply `ArchPagingMeta::make_private_address` before
    /// storing it in an entry.
    fn allocate_table_page() -> (ret: Result<
        (PhysAddr, Tracked<PTPageInit<A>>),
        PagingError,
    >)
        ensures
            ret matches Ok((paddr, page)) ==> {
                &&& page@.wf()
                &&& page@.base == A::spec_paddr_to_vaddr(
                    paddr@,
                )
                // Clean: within the address field, and neither tag set, so the
                // page table is free to tag it either way.
                &&& paddr@ & !A::spec_address_mask() == 0
                &&& paddr@ & A::spec_private_mask() == 0
                &&& paddr@ & A::spec_shared_mask() == 0
            },
    ;

    /// Returns a frame to the allocator, taking back the ownership of its words
    /// that [`Self::allocate_table_page`] gave up.
    fn deallocate_table_page(
        paddr: PhysAddr,
        Tracked(page): Tracked<PTPageInit<A>>,
    )
        requires
            page.wf_owned(),
            page.base == A::spec_paddr_to_vaddr(paddr@),
    ;

    /// Invalidates the cached translations of `[start, end)` on every
    /// processor that may be walking this table.
    ///
    /// Which processors those are, and whether reaching them takes an IPI, is
    /// the OS's to know; the page table only says which addresses changed. It
    /// is always correct to flush more than asked.
    fn flush_range(start: usize, end: usize)
        opens_invariants none
    ;

    /// The lock guarding the table page `page` points at.
    ///
    /// Returning a `&'static` is what makes the inner level of locking
    /// reachable from anywhere in a walk: a thread that has descended to a page
    /// can lock it having been handed nothing but the page's address.
    fn page_lock(page: *mut PTPage<A>) -> (ret: &'static Self::PageLock)
        ensures
            ret.page() == page@.addr,
    ;
}

/// The reader token of one slot, as the walk layer names it.
pub type SlotShared<A> = RWShared<PTEntry<A>, Option<PTPageSharedPerm<A>>>;

} // verus!

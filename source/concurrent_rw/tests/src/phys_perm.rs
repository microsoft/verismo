//! A worked client of [`AnyPointsTo`]: a permission that names a *physical frame*, read through
//! a page table.
//!
//! The identity impl in the library names a location by the address it is at, so the two
//! coincide and `resolves_to` is address equality. This is the case where they come apart. A
//! [`PhysPointsTo`] names a physical address and knows no virtual one; what turns it into
//! something the hardware can be handed is a page table, supplied per access as the evidence.
//!
//! Two consequences worth reading the code for. First, no virtual address appears in the
//! permission, so a client's specifications are stated in frames -- the thing that is stable --
//! rather than in whatever address the frame happens to be mapped at. Second, because the
//! evidence is per access rather than baked in, the *same* permission can be read through two
//! different page tables, which is what `example_two_address_spaces` shows.
//!
//! [`PhysPointsTo::borrow_at`] is trusted, and is the only trusted thing here: no proof can
//! establish that a virtual address reaches a frame, because that is a fact about the hardware's
//! translation, not about the token. It is stated as an `external_body` proof fn whose `requires`
//! names exactly the assumption -- a page table that translates the address to the frame.
use concurrent_rw::*;
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::pt::{Extra, PTEntry};
#[cfg(verus_only)]
use vstd::raw_ptr::PointsTo;

verus! {

/// A permission to one machine word, named by the physical address it lives at.
///
/// The type parameter is the value's type; `frame` is where it is, and there is deliberately no
/// field saying where it is *mapped*.
pub tracked struct PhysPointsTo<T> {
    ghost dummy: core::marker::PhantomData<T>,
}

impl<T> PhysPointsTo<T> {
    /// The physical address this permission is for.
    pub uninterp spec fn frame(&self) -> usize;

    pub uninterp spec fn spec_value(&self) -> T;

    pub uninterp spec fn spec_is_init(&self) -> bool;
}

/// The evidence: a page table, viewed as the translation it performs.
///
/// Tracked rather than ghost because holding it is what a reader must actually do -- a
/// translation that no longer exists is not evidence, and dropping the token is how a client
/// gives up the right to read through it.
pub tracked struct PTPerm {
    ghost dummy: usize,
}

impl PTPerm {
    /// What this page table translates `vaddr` to, if anything.
    pub uninterp spec fn translate(&self, vaddr: usize) -> Option<usize>;
}

impl<T> AnyPointsTo<T> for PhysPointsTo<T> {
    type Evidence = PTPerm;

    type Id = usize;

    open spec fn id(&self) -> usize {
        self.frame()
    }

    open spec fn value(&self) -> T {
        self.spec_value()
    }

    open spec fn is_init(&self) -> bool {
        self.spec_is_init()
    }

    /// An address resolves to a frame exactly when this page table says it does.
    open spec fn resolves_to(ev: &PTPerm, ptr: *mut T, id: usize) -> bool {
        ev.translate(ptr@.addr) == Some(id)
    }

    /// **Trusted.** That a virtual address reaches a frame is a fact about the hardware's
    /// translation; nothing in the token can witness it, so it is assumed here against a page
    /// table that performs it.
    #[verifier::external_body]
    proof fn borrow_at<'a>(tracked &'a self, ptr: *mut T, tracked ev: &PTPerm) -> (tracked ret:
        &'a PointsTo<T>) {
        unimplemented!()
    }
}

/// The permission is stated in frames, and an address is supplied only to read it.
///
/// What comes back is an ordinary `PointsTo` at `ptr`, which is what makes this usable: the
/// caller can hand it to an atomic load without the load knowing anything about frames.
pub proof fn example_read_through_page_table<'a>(
    tracked perm: &'a PhysPointsTo<usize>,
    tracked pt: &PTPerm,
    ptr: *mut usize,
) -> (tracked ret: &'a PointsTo<usize>)
    requires
        perm.is_init(),
        pt.translate(ptr@.addr) == Some(perm.frame()),
    ensures
        ret.ptr() == ptr,
        ret.is_init(),
        ret.value() == perm.value(),
{
    perm.borrow_at(ptr, pt)
}

/// One frame, two address spaces: because the page table is an argument rather than a field, the
/// same permission reads the same value at two unrelated addresses.
pub proof fn example_two_address_spaces(
    tracked perm: &PhysPointsTo<usize>,
    tracked pt_a: &PTPerm,
    tracked pt_b: &PTPerm,
    ptr_a: *mut usize,
    ptr_b: *mut usize,
)
    requires
        perm.is_init(),
        pt_a.translate(ptr_a@.addr) == Some(perm.frame()),
        pt_b.translate(ptr_b@.addr) == Some(perm.frame()),
{
    let tracked seen_a = perm.borrow_at(ptr_a, pt_a);
    let tracked seen_b = perm.borrow_at(ptr_b, pt_b);
    assert(seen_a.value() == seen_b.value());
}

/// The payoff: the token types are generic in the permission, so a shared location can be named
/// by the frame it lives in rather than by an address it is mapped at.
///
/// `location()` here *is* a physical address. A client built this way states its invariants in
/// frames, and the virtual address enters only at the moment of an access.
pub proof fn example_phys_keyed_shared(
    tracked perm: PhysPointsTo<usize>,
    tracked payload: Extra,
    value: PTEntry,
) -> (tracked ret: (
    RWShared<PTEntry, Extra, PhysPointsTo<usize>>,
    WritePerm<PTEntry>,
    Observed<PTEntry>,
))
    requires
        perm.is_init(),
        perm.value() == value.value,
        value.wf_payload(payload),
        !value.has_published_payload(),
    ensures
        ret.0.location() == perm.frame(),
{
    RWShared::new(value, perm, payload)
}

} // verus!

//! **Trusted spec.** What names a location, and what it takes to read one.
//!
//! The crate does not care that a location is a raw pointer. It cares that a permission names
//! *some* location, that no two permissions name the same one, and that a holder can turn one
//! into a `PointsTo` at the address the hardware will actually be given. That is this trait.
//!
//! The identity impl for [`vstd::raw_ptr::PointsTo`] is in `tokens_impl` and is proved, not
//! assumed: a `PointsTo` names its own address, and the evidence that an address reaches it is
//! the address matching. An implementor that names locations *physically* is a different
//! matter -- only the OS can say which virtual address reaches a frame, so such an impl is
//! trusted, and it is trusted in the client, not here.
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::raw_ptr::PointsTo;

verus! {

/// A permission to a location that names the location itself.
///
/// [`Self::borrow_at`] is the whole point: it is the only way the crate reaches memory, so an
/// implementor that gets it wrong is an implementor that can read the wrong address. Its
/// `requires` is what an implementor may demand in exchange -- nothing, for a permission that
/// already knows its address; a mapping, for one that does not.
pub trait AnyPointsTo<T>: Sized {
    /// What the caller must show to read this permission at a given address.
    ///
    /// `()` for a permission that names an address directly. A permission that names a physical
    /// frame needs the OS's word that the address reaches it.
    type Evidence;

    /// How this permission names its location: an address, a frame, an index in a region.
    type Id;

    spec fn id(&self) -> Self::Id;

    spec fn value(&self) -> T;

    spec fn is_init(&self) -> bool;

    /// Under `ev`, whether `ptr` resolves to the location named `id`.
    ///
    /// A relation, not a function: one location may resolve from more than one address, which is
    /// the ordinary case for a frame mapped into two address spaces.
    spec fn resolves_to(ev: &Self::Evidence, ptr: *mut T, id: Self::Id) -> bool;

    /// The location, as a pointer permission the hardware can be handed.
    ///
    /// Borrowed rather than exchanged: the permission stays where it is, so this can be called
    /// under a `&` inside an invariant block without having to put anything back.
    proof fn borrow_at<'a>(
        tracked &'a self,
        ptr: *mut T,
        tracked ev: &Self::Evidence,
    ) -> (tracked ret: &'a PointsTo<T>)
        requires
            Self::resolves_to(ev, ptr, self.id()),
            self.is_init(),
        ensures
            ret.ptr() == ptr,
            ret.is_init(),
            ret.value() == self.value(),
    ;
}

} // verus!

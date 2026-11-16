//! **Trusted spec.** What names a location, and what it takes to reach one.
//!
//! The crate does not care that a location is a raw pointer. It cares that a permission names
//! *some* location, that no two permissions name the same one, and that a holder can turn one
//! into a `PointsTo` at the address the hardware will actually be given. That is this trait, and
//! it is what makes the whole of `protocol::contract` work over any permission a client picks:
//! `RWModel::Perm` names the one it chose.
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
/// [`Self::borrow_at`] and [`Self::borrow_mut_at`] are the whole point: they are the only way the
/// crate reaches memory, so an implementor that gets them wrong is an implementor that can read or
/// write the wrong address. Their `requires` is what an implementor may demand in exchange --
/// nothing, for a permission that already knows its address; a mapping, for one that does not.
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

    /// [`Self::borrow_at`] for a store: the same borrow, mutably.
    ///
    /// A store needs a `&mut PointsTo`, so a permission that only ever lends `&` can be read
    /// through but never written.
    ///
    /// The lend is only meaningful if it is given back at the address it was taken at -- a caller
    /// is free to overwrite a `&mut` with a permission to somewhere else entirely, and nothing
    /// could then be said about where the store landed. Hence the hypothesis on the final clauses,
    /// which is what a store satisfies: the location is unchanged, so whatever named this
    /// permission still does, and the value is mirrored, so the store lands in the permission
    /// rather than only in the borrow.
    proof fn borrow_mut_at<'a>(
        tracked &'a mut self,
        ptr: *mut T,
        tracked ev: &Self::Evidence,
    ) -> (tracked ret: &'a mut PointsTo<T>)
        requires
            Self::resolves_to(ev, ptr, old(self).id()),
            old(self).is_init(),
        ensures
            ret.ptr() == ptr,
            ret.is_init(),
            ret.value() == old(self).value(),
            final(ret).ptr() == ptr ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self).is_init() == final(ret).is_init()
                &&& final(self).value() == final(ret).value()
            },
    ;
}

} // verus!

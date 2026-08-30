//! Everything this crate assumes, in one place.
//!
//! [`points_to`](super::points_to) derives its permissions from address tokens;
//! this module is the handful of steps that cannot be derived, gathered here so
//! that reviewing what is trusted means reviewing one file.
//!
//! There are six, in two groups.
//!
//! **Owning the tokens is owning the memory.** vstd's memory is indexed by
//! address and knows nothing of an MMU, so nothing in it says that owning a
//! virtual range and the physical range beneath it owns any bytes at all.
//! [`GeneralPointsTo::borrow`], [`GeneralPointsTo::borrow_mut`] and
//! [`GeneralPointsTo::into_points_to`] are one assumption in three signatures --
//! shared, mutable, by value -- and [`GeneralPointsTo::borrow_mut_via_pt`] is
//! the same for a pointer reached by a page walk rather than by the alias set.
//!
//! **Rust lays an array out as its elements.** [`axiom_array_layout`] for the
//! addresses, [`points_to_array_split`] for the ownership.
use vstd::layout::{align_of, size_of};
use vstd::prelude::*;
use vstd::raw_ptr::{MemContents, PointsTo};

use super::points_to::{array_element_ptr, GeneralPointsTo, PageWalkPath};
use crate::ArchPagingMeta;

verus! {

/// **Assumption.** An array is its elements, laid out end to end.
///
/// Rust guarantees this -- `[T; N]` is `N` contiguous `T`s, aligned as a `T` --
/// but vstd's [`size_of`] and [`align_of`] are uninterpreted, so nothing in it
/// relates the two.
pub broadcast axiom fn axiom_array_layout<T, const N: usize>()
    ensures
        #[trigger] size_of::<[T; N]>() == N * size_of::<T>(),
        align_of::<[T; N]>() == align_of::<T>(),
;

/// **Assumption.** A permission to an array is permission to each of its
/// elements, each keeping the value it had.
///
/// The counterpart of [`axiom_array_layout`] for ownership rather than for
/// addresses. vstd's [`PointsTo`] is opaque, and its only route from an array
/// permission to its parts insists the memory be uninitialized -- which is the
/// one case this must not be limited to.
pub axiom fn points_to_array_split<T, const N: usize>(tracked pt: PointsTo<[T; N]>) -> (tracked ret:
    Seq<PointsTo<T>>)
    requires
        pt.is_init(),
    ensures
        ret.len() == N,
        forall|i: int|
            #![trigger ret[i]]
            0 <= i < N ==> {
                &&& ret[i].ptr() == array_element_ptr(pt.ptr(), i)
                &&& ret[i].opt_value() == MemContents::Init(pt.value()[i])
            },
;

impl<T, A: ArchPagingMeta> GeneralPointsTo<T, A> {
    /// **Assumption.** Holding the address tokens for an alias is holding the
    /// memory it reaches, so a vstd permission for it can be handed out.
    pub axiom fn borrow(tracked &self, ptr: *mut T) -> (tracked ret: &PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == self.opt_value(),
    ;

    /// **Assumption.** [`Self::borrow`] in mutable form, which is also where
    /// aliasing gets its meaning: every alias yields the *same* value, so a
    /// write through this one is what all the others then read.
    ///
    /// Stated on a mutable borrow rather than as a separate "resynchronize"
    /// step so that exec code can keep writing through an ordinary
    /// `&mut PointsTo`.
    ///
    /// The final clause is what stops a borrow from returning as a permission
    /// to *different* memory: an axiom assumes arbitrary behaviour for whatever
    /// it leaves unsaid, so without it a borrow could come back with fresh
    /// address tokens, and two permissions claiming one frame would let the
    /// address space's hand-each-address-out-once guarantee prove `false`.
    pub axiom fn borrow_mut(tracked &mut self, ptr: *mut T) -> (tracked ret: &mut PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == old(self).opt_value(),
            final(ret).opt_value() == final(self).opt_value(),
            final(self).same_except_value(old(self)),
    ;

    /// **Assumption.** [`Self::borrow_mut`] through a *translation* rather than
    /// through the alias set: the walk proves `ptr` reaches this memory, which
    /// is how a pointer the permission has never seen -- a recursive-map alias,
    /// say -- can still be used to write it.
    ///
    /// A walk is a proof about the *page tables*; only the hardware turns that
    /// into a statement about which bytes a pointer reaches.
    ///
    /// `pa` is the address of the object, not of its frame. That is what makes
    /// the pairing sound: two objects in one frame have the same frame and
    /// different addresses, so a frame-level match would let a caller reach the
    /// wrong word through a correct walk.
    ///
    /// The alias is *not* added to [`Self::ptrs`]: it lasts exactly as long as
    /// the borrow of `walk`, and the walk borrows every entry permission along
    /// the path, so the mapping cannot be torn down while the alias is in use.
    /// A durable alias would have to be justified by something the permission
    /// keeps hold of -- otherwise unmapping `ptr` would leave a permission
    /// claiming a pointer that no longer reaches it -- and nesting the entry
    /// permissions cannot supply that, because a self-mapped root's permission
    /// would have to contain itself.
    pub axiom fn borrow_mut_via_pt(
        tracked &mut self,
        pa: usize,
        ptr: *mut T,
        tracked walk: &PageWalkPath<A>,
    ) -> (tracked ret: &mut PointsTo<T>)
        requires
            old(self).is_at_phys_addr(pa as int),
            walk.can_translate_to_phys_addr(ptr@.addr, pa),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == old(self).opt_value(),
            final(ret).opt_value() == final(self).opt_value(),
            final(self).same_except_value(old(self)),
    ;

    /// **Assumption.** [`Self::borrow`] by value: keeping one alias, and giving
    /// up every token in exchange for a plain vstd permission to it.
    pub axiom fn into_points_to(tracked self, ptr: *mut T) -> (tracked ret: PointsTo<T>)
        requires
            self.covers(ptr),
        ensures
            ret.ptr() == ptr,
            ret.opt_value() == self.opt_value(),
    ;
}

} // verus!

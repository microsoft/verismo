//! A `PointsTo` as an [`AnyPointsTo`]: the case where a permission already names an address.
//!
//! Nothing here is assumed. A `PointsTo` names the address it points at, the evidence that an
//! address reaches it is the address being that one, and `borrow_at` hands back the permission
//! itself. This is the impl the crate's own executable reads and writes run on; a client that
//! names locations some other way supplies its own.
use vstd::prelude::*;
use vstd::raw_ptr::PointsTo;

use crate::protocol::perm::AnyPointsTo;

verus! {

impl<T> AnyPointsTo<T> for PointsTo<T> {
    type Evidence = ();

    type Id = *mut T;

    open spec fn id(&self) -> *mut T {
        self.ptr()
    }

    open spec fn value(&self) -> T {
        self.opt_value()->Init_0
    }

    open spec fn is_init(&self) -> bool {
        self.is_init()
    }

    open spec fn resolves_to(ev: &(), ptr: *mut T, id: *mut T) -> bool {
        ptr == id
    }

    proof fn borrow_at<'a>(tracked &'a self, ptr: *mut T, tracked ev: &()) -> (tracked ret:
        &'a PointsTo<T>) {
        self
    }
}

} // verus!

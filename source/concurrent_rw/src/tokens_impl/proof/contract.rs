//! **The bridge.** Proves [`crate::tokens_impl`] satisfies [`crate::protocol::contract`].
//!
//! Checked, not read. Every impl is a delegation to the operation that already exists; the work
//! is in the rest of `tokens_impl`, and what this file adds is the obligation to have done all of
//! it. A guarantee stated in the contract and missing here is a compile error.
//!
//! It sits here rather than under `protocol/` because it belongs to this construction, not to the
//! interface: `protocol/` is what a client reads, and this is one particular way of satisfying
//! it. Swap `tokens_impl` for a different construction and this is the file that goes with it.
use vstd::prelude::*;

use crate::tokens_impl::payload_slot::PayloadTicket;
use crate::tokens_impl::*;
#[cfg(verus_only)]
use vstd::invariant::OpenInvariantCredit;
#[cfg(verus_only)]
use vstd::raw_ptr::PointsTo;
#[cfg(verus_only)]
use vstd::{open_atomic_invariant, open_atomic_invariant_in_proof};

verus! {

// The proofs behind `protocol::contract::RWWithPublishPayloadContract`, the published-payload half.
// Bounded on `PublishPayload`, so a model that never publishes gets neither the obligations nor
// the API.
impl<
    T: PublishPayload<AtomicType = usize> + From<usize> + Into<usize>,
> crate::protocol::contract::RWWithPublishPayloadContract for T where usize: From<T> {
    fn read_published(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(past): Tracked<Option<&Observed<Self>>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>, Tracked<Option<PayloadTicket<Self::Payload>>>)) {
        crate::tokens_impl::rw_proof::rw_exec::read_published(ptr, Tracked(r), Tracked(past))
    }

    proof fn payloads_agree(
        tracked t1: &PayloadTicket<Self::Payload>,
        tracked t2: &PayloadTicket<Self::Payload>,
    ) {
        t1.agree(t2)
    }

    fn write_with_published_payload(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (Tracked<Observed<Self>>, Tracked<PayloadTicket<Self::Payload>>)) {
        crate::tokens_impl::rw_proof::rw_exec::write_with_published_payload(
            ptr,
            value,
            Tracked(r),
            Tracked(w),
            Tracked(payload),
        )
    }

    fn write_published_unrestricted(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (
        Tracked<RWShared<Self, Self::Payload>>,
        Tracked<Observed<Self>>,
        Tracked<PayloadTicket<Self::Payload>>,
    )) {
        crate::tokens_impl::rw_proof::rw_exec::write_published_unrestricted(
            ptr,
            value,
            Tracked(r),
            Tracked(w),
            Tracked(payload),
        )
    }
}

// The proofs behind `protocol::contract::RWContract`. Each body delegates to the operation that
// already exists; the trait exists so a reader can find the guarantees in one place, and so that
// a guarantee stated there but not proved here fails to compile.
impl<
    T: RWModel<AtomicType = usize> + From<usize> + Into<usize>,
> crate::protocol::contract::RWContract for T where usize: From<T> {
    proof fn build_rw(
        value: Self,
        tracked points_to: PointsTo<Self::AtomicType>,
        tracked payload: Self::Payload,
    ) -> (tracked ret: (RWShared<Self, Self::Payload>, WritePerm<Self>, Observed<Self>)) {
        let tracked out = RWShared::<Self, Self::Payload>::new(value, points_to, payload);
        out
    }

    proof fn teardown_rw(
        tracked r: RWShared<Self, Self::Payload>,
        tracked w: WritePerm<Self>,
    ) -> (tracked ret: (PointsTo<Self::AtomicType>, Self::Payload)) {
        r.teardown(w)
    }

    fn read(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(past): Tracked<Option<&Observed<Self>>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>)) {
        crate::tokens_impl::rw_proof::rw_exec::read(ptr, Tracked(r), Tracked(past))
    }

    fn read_exact(
        ptr: *mut Self::AtomicType,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&WritePerm<Self>>,
    ) -> (ret: (Self, Tracked<Observed<Self>>)) {
        crate::tokens_impl::rw_proof::rw_exec::read_exact(ptr, Tracked(r), Tracked(w))
    }

    fn write(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
    ) -> (ret: Tracked<Observed<Self>>) {
        crate::tokens_impl::rw_proof::rw_exec::write(ptr, value, Tracked(r), Tracked(w))
    }

    fn write_with_payload(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<&RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: Tracked<Observed<Self>>) {
        crate::tokens_impl::rw_proof::rw_exec::write_with_payload(
            ptr,
            value,
            Tracked(r),
            Tracked(w),
            Tracked(payload),
        )
    }

    fn write_unrestricted(
        ptr: *mut Self::AtomicType,
        value: Self,
        Tracked(r): Tracked<RWShared<Self, Self::Payload>>,
        Tracked(w): Tracked<&mut WritePerm<Self>>,
        Tracked(payload): Tracked<Self::Payload>,
    ) -> (ret: (Tracked<RWShared<Self, Self::Payload>>, Tracked<Observed<Self>>)) {
        crate::tokens_impl::rw_proof::rw_exec::write_unrestricted(
            ptr,
            value,
            Tracked(r),
            Tracked(w),
            Tracked(payload),
        )
    }
}

} // verus!

//! The numbering of instance ids that this crate takes on faith.
//!
//! [`loc_to_int`] is assumed for a different reason -- not because it is unprovable, but because
//! the definition that would prove it is out of reach until Verus issue #2735 lands.
//!
//! There used to be a third atomic-side assumption, `frac_bounded2`, needed to show a reader
//! could reuse one `Observed` token across reads. Observations are no longer fractional -- they
//! are duplicable membership in a set that only grows -- so nothing needs it.
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::tokens::InstanceId;

verus! {

/// A number naming an instance, used to give each `AtomicInvariant` a distinct namespace.
///
/// Uninterpreted only because `InstanceId` has no public ordering to define it from; Verus
/// issue #2735 would supply one, and then this and the axiom below both go away.
pub uninterp spec fn loc_to_int(id: InstanceId) -> int;

/// Distinct instances get distinct numbers.
#[verifier::external_body]
pub broadcast proof fn axiom_loc_to_int_injective(a: InstanceId, b: InstanceId)
    ensures
        #[trigger] loc_to_int(a) == #[trigger] loc_to_int(b) ==> a == b,
{
}

/// The usable direction: different instances, different numbers. Proved from the axiom above.
pub proof fn loc_to_int_distinct(a: InstanceId, b: InstanceId)
    requires
        a != b,
    ensures
        loc_to_int(a) != loc_to_int(b),
{
    axiom_loc_to_int_injective(a, b);
}

} // verus!

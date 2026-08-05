//! **The construction.** One way of building tokens that satisfy
//! [`crate::protocol::contract`].
//!
//! The contract says what a `RWShared`, `WritePerm`, `Observed` and `PayloadTicket` are *for*. This
//! module says what they *are*. Nothing here needs to be believed: [`contract_proof`]
//! checks it against the contract, and a client that reads only `protocol` misses nothing.
//!
//! Everything rests on one idea. Each token is a *fractional share* of a ghost resource, and what
//! you may do depends on how much you hold. Entirely ghost; the operations that touch the pointer
//! live in [`rw_proof::rw_exec`].
//!
//! ```text
//!     PointsTo<AtomicType>        exclusive: no read may run during a write
//!            |  RWShared::new       (the contract calls this RWContract::build_rw)
//!            v
//!     WritePerm + RWShared + Observed  reads and the write may now overlap
//! ```
//!
//! # `WritePerm` -- half the value
//!
//! The value lives in a `FracGhost<T>` split in two: [`WritePerm`] holds one half, `RWState`
//! holds the other inside the reader's invariant. Neither can change the value alone, so a store
//! must open the invariant and bring them together. Holding half is also the `WritePerm`'s type
//! invariant, so a second `WritePerm` cannot be built -- there is no second half to build it from.
//! That, and not a lock, is what "single writer" means here.
//!
//! # `RWShared` -- held by every reader, opened by the writer too
//!
//! [`RWShared`] is a handle on the `AtomicInvariant` holding `RWState`, plus a handle on the
//! payload slot. There is one per pointer, but a read needs only `&RWShared`, so that one token
//! can be shared across threads. The writer opens the same invariant, which is why reads and the
//! write may overlap: consistency comes from the invariant, not from keeping them apart.
//!
//! # `Observed` -- evidence that a pair was once current
//!
//! [`Observed`] is duplicable evidence of membership in `RWState::obs`, one `ObsHistory`
//! holding every value-and-payload pair anyone has seen. The set only grows, and the invariant
//! says the pair now is reachable from every pair in it. Evidence about the past therefore
//! becomes a claim about every future read -- property 1 of [`crate::protocol::contract`] --
//! and the writer's `write_value_requires` is what keeps it true.
//!
//! # The payload
//!
//! Beside the value, `RWState` holds a `PayloadHolder` -- tracked data too large or too
//! non-copyable to live in the value itself. The invariant keeps `value.has_published_payload()`
//! equal to whether the slot really has, so the value cannot lie about it. That equation holds
//! for every model, which is why `has_published_payload` sits in `RWModel` rather than in
//! `PublishPayload`; it defaults to `false`, so a model that never publishes writes nothing.
//!
//! Unpublished, the payload is reachable by anyone -- a read opens the same invariant a write does
//! -- but only from inside the block, and a block admits one atomic operation plus ghost code, so
//! no ordinary work can run while holding it. Nor is anything promised across threads: the writer
//! may replace it before anyone looks again.
//!
//! Publishing lifts both limits. `slot_version` lives in `RWConstant`, so every ticket is
//! minted at one version and `payloads_agree` pins them all to a single payload for the
//! `RWShared`'s whole life; and `wf_payload` is re-derived from the invariant on each read, so the
//! payload stays well-formed against whatever you read. Tickets are neither unique nor consumed:
//! borrowing takes `&PayloadTicket`, and every read of a published value mints another. Property
//! 3b is what makes that harmless.
//!
//! A payload leaves the slot only through `PayloadHolder::reclaim`, which consumes the reader's
//! `SlotHandle` and bumps the version. Nothing here calls it yet, so publishing is one-way in
//! practice.
/// The fractional-permission ghost resource, verified here from a tokenized state machine.
/// Adapted from coconut-svsm. Only the `state_machine` implementation uses it; without that
/// feature the crate uses `vstd::resource::frac::FracGhost` instead.
#[cfg(all(feature = "state_machine", verus_only))]
#[path = "proof/frac_perm.rs"]
pub mod frac_perm_proof;

// The versioned payload slot. Two implementations of one API, both named `payload_slot` so
// that use sites need no cfg:
//
// * without `--features state_machine`: built on vstd's `StorageResource` protocol;
// * with it: built on a tokenized state machine, verified here.
//
// The type naming a slot instance is the whole of the difference, and the `SlotId` alias in
// `SlotId` alias below absorbs that.
#[cfg(any(not(feature = "state_machine"), not(verus_only)))]
#[path = "proof/payload_slot.rs"]
pub mod payload_slot;
#[cfg(all(feature = "state_machine", verus_only))]
#[path = "proof/payload_slot_sm.rs"]
pub mod payload_slot;

// The observed set, in the same two-implementations shape. No ready-made vstd set serves: the
// observed set must be persistent, and every persistent set there is `reject_recursive_types`,
// which a snapshot -- a value paired with a payload, and payloads hold readers -- is not. So
// both are built here, one on a hand-written resource algebra and one on a state machine.
#[cfg(any(not(feature = "state_machine"), not(verus_only)))]
#[path = "proof/obs_history.rs"]
pub mod obs_history;
#[cfg(all(feature = "state_machine", verus_only))]
#[path = "proof/obs_history_sm.rs"]
pub mod obs_history;

/// The token types and their ghost operations -- everything described above. Re-exported below,
/// so `tokens_impl::RWShared` still names a `RWShared`. `rw_exec`, the executable reads and writes,
/// is a child of it, and stays crate-private: `crate::protocol::contract` is the way in.
#[path = "proof/rw.rs"]
pub mod rw_proof;

/// Discharges [`crate::protocol::contract`] against the types below. Checked, not read: every
/// impl is a delegation, and a guarantee stated in the contract and missing there is a compile
/// error.
#[path = "proof/contract.rs"]
pub mod contract_proof;
pub use rw_proof::*;

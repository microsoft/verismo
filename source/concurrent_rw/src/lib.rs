//! Multiple-reader single-writer tokens over a shared atomic value -- second implementation.
//!
//! A value of an atomic type, behind a raw pointer, is split into a
//! [`Writer`](tokens_impl::Writer) (exclusive, and required in order to store) and a
//! [`Reader`](tokens_impl::Reader), which a read needs only by `&`, so it can be shared.
//! A read returns the value together with an [`Observed`](tokens_impl::Observed) token proving
//! *this* reader saw *that* value *with that payload beside it*, and the client's
//! [`RWModel`](tokens_impl::RWModel) impl says which pairs a reader may observe next. A tracked
//! payload lives in a versioned slot that readers borrow for as long as their `Observed` token
//! stays current.
//!
//! Two modules are the ones to read: [`protocol`] is the interface -- what a client supplies and
//! what the crate guarantees back -- and [`trusted_t`] is what the crate assumes. Everything else
//! is checked against them.
//!
//! # Running the verifier
//!
//! ```text
//! verus src/lib.rs --crate-type=lib
//! verus src/lib.rs --crate-type=lib --cfg 'feature="state_machine"'
//! cargo verus verify
//! cargo verus verify --features state_machine
//! ```
#![no_std]
#![cfg_attr(verus_keep_ghost, allow(unexpected_cfgs))]
#![cfg_attr(not(verus_only), allow(dead_code))]

/// **The specification.** What a client supplies, and what the crate guarantees back. Trusted:
/// read these two files and nothing else.
pub mod protocol;

/// **What the crate assumes.** A numbering of instance ids.
pub mod trusted_t;

/// **The construction.** One way of building tokens that satisfy [`protocol::contract`]:
/// the token types, their ghost operations, the executable reads and writes over them, and
/// [`tokens_impl::contract_proof`], which discharges the contract against them.
pub mod tokens_impl;

// Everything a client needs, at the crate root. `protocol` is what to read; these are the same
// items, spelled shorter.
//
// The traits a client implements, and the guarantees they buy.
pub use protocol::contract::{RWContract, RWWithPublishPayloadContract};
pub use protocol::model::{IsValidAtomicType, PublishPayload, RWModel, Snapshot, WithPayload};

// The tokens. The operations over them are trait methods on `RWContract` and
// `RWWithPublishPayloadContract` above -- there is no second, looser way in.
pub use tokens_impl::payload_slot::{PayloadHolder, PayloadTicket, SlotHandle};
pub use tokens_impl::{Observed, Reader, ReaderConstant, ReaderState, Writer};

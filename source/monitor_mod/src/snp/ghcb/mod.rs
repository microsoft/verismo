mod def_s;
#[macro_use]
mod proto_s;
mod proto_e;
mod proto_impl;
mod proto_page;

pub use def_s::*;
pub use proto_e::*;
pub use proto_impl::*;
pub use proto_page::*;
pub use proto_s::*;

use super::cpu::Vmsa;
use super::trackedcore::*;
use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::attack::*;
use crate::arch::reg::*;
use crate::ptr::*;
use crate::registers::*;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::*;

pub type GhcbHandle = crate::vbox::VBox<GhcbPage>;
#[macro_export]
macro_rules! SVM_EVTINJ_IS_VALID {
    ($x: expr) => {
        bit_check($x, SVM_EVTINJ_VALID_BIT)
    };
}

#[macro_export]
macro_rules! GHCB_MSR_PROTOCOL_MIN {
    ($x: expr) => {
        (($x) >> 32) & 0xffff
    };
}

#[macro_export]
macro_rules! GHCB_MSR_PROTOCOL_MAX {
    ($x: expr) => {
        (($x) >> 48) & 0xffff
    };
}

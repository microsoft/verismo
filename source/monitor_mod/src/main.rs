#![no_std] // don't link the Rust standard library
#![no_main] // disable all Rust-level entry points
#![feature(panic_info_message)]
#![allow(unused)]

#[cfg(target_os = "none")]
core::arch::global_asm!(include_str!("entry.s"), options(att_syntax));

use core::panic::PanicInfo;

use monitor_mod::debug::VEarlyPrintAtLevel;
use monitor_mod::snp::ghcb::*;
use vstd::prelude::*;
use vstd::string::*;

#[panic_handler]
#[verifier::external]
fn panic(info: &PanicInfo) -> ! {
    new_strlit("panic:\n").err(Tracked::assume_new());
    match info.message() {
        Some(msg) => {
            if msg.as_str().is_some() {
                StrSlice::from_rust_str(msg.as_str().unwrap()).err(Tracked::assume_new());
            }
        }
        None => todo!(),
    }

    if let Some(location) = info.location() {
        (StrSlice::from_rust_str(location.file()), location.line()).err(Tracked::assume_new());
    } else {
        new_strlit("Panic occurred but no location information available")
            .err(Tracked::assume_new());
    }
    vc_terminate(SM_TERM_UNSUPPORTED, Tracked::assume_new());

    loop {}
}

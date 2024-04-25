use std::env;
use std::fs::File;
use std::io::Write;
use std::process::Command;

fn main() {
    // Environment vars during build.
    if cfg!(feature = "noverify") {
        println!("cargo:rustc-env=VERUS_ARGS=--no-verify");
    } else {
        println!("cargo:rustc-env=VERUS_ARGS=--rlimit=8000 --expand-errors --multiple-errors=5 --triggers-silent --time-expanded --no-auto-recommends-check --output-json --trace");
    }

    let module_path = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-env=MODULE_PATH={}", module_path);

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MODULE");
}

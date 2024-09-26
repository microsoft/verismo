use std::env;
use std::fs::File;
use std::io::Write;
use std::process::Command;

fn main() {
    // Environment vars during build.
    if cfg!(feature = "noverify") {
        println!("cargo:rustc-env=VERUS_ARGS=--no-verify --no-builtin");
    } else {
        let verus_args = [
            "--rlimit=8000",
            "--no-builtin",
            "--expand-errors",
            "--multiple-errors=5",
            "--triggers-silent",
            "--time-expanded",
            "--no-auto-recommends-check",
            "--output-json",
            "--trace",
        ];
        println!("cargo:rustc-env=VERUS_ARGS={}", verus_args.join(" "));
    }

    let target = env::var("CARGO_PKG_NAME").unwrap_or_default();
    println!("cargo:rustc-env=VERUS_TARGETS={}", target);
    for (key, value) in env::vars() {
        // You can filter or modify which ones to pass to rustc
        println!("cargo:rustc-env={}={}", key, value);
    }

    let module_path = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-env=MODULE_PATH={}", module_path);

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MODULE");
}

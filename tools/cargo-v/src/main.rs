use signal_hook::consts::SIGINT;
use signal_hook::consts::SIGTERM;
use signal_hook::iterator::Signals;
use std::env;
use std::ffi::OsStr;
use std::process::{exit, Command};

fn main() {
    // Install and activate
    let args: Vec<String> = env::args().collect();

    match args[0].as_str() {
        "build" => {}
        _ => {
            unimplemented!();
        }
    }

    install();

    // Set up signal handling
    let mut signals = Signals::new(&[SIGINT, SIGTERM]).expect("Unable to set up signal handling");
    let handle = std::thread::spawn(move || {
        for _ in signals.forever() {
            deactivate();
            exit(0);
        }
    });
    activate();

    // Run cargo build with additional arguments
    let status = Command::new("cargo")
        .args(&args)
        .status()
        .expect("Failed to execute cargo build");

    if !status.success() {
        eprintln!("cargo build failed with status: {}", status);
    }

    deactivate();

    // Wait for the signal handling thread to finish
    handle.join().expect("Signal handling thread has panicked");
}

fn install() {
    // Get the verus revision
    let output = Command::new("cargo")
        .arg("tree")
        .output()
        .expect("Failed to execute cargo tree");

    let out = String::from_utf8_lossy(&output.stdout);
    let verus_rev = out
        .lines()
        .find(|line| line.contains("builtin_macros"))
        .map(|line| {
            line.split("rev=")
                .nth(1)
                .and_then(|s| s.split('#').next())
                .unwrap_or("")
        })
        .unwrap_or("");

    println!("Using verus commit {}", verus_rev);

    let verus_rust_version = "nightly-2023-12-22";
    let status = Command::new("cargo")
        .arg("install")
        .arg("--git")
        .arg("https://github.com/microsoft/verismo/")
        .arg("verus-rustc")
        .env("VERUS_RUST_VERSION", verus_rust_version)
        .env("VERUS_REV", verus_rev)
        .status()
        .expect("Failed to execute cargo install");

    if !status.success() {
        eprintln!("cargo install failed with status: {}", status);
    }
}

fn activate() {
    // Set the rustup override and RUSTC variable
    let status = Command::new("rustup")
        .arg("override")
        .arg("set")
        .arg("nightly-2023-12-22")
        .status()
        .expect("Failed to execute rustup override");

    if !status.success() {
        eprintln!("rustup override set failed with status: {}", status);
    }

    // Set the RUSTC variable (note: this only sets it for this process)
    env::set_var("RUSTC", "verus-rustc");
    println!("Set RUSTC = verus-rustc");
}

fn deactivate() {
    // Unset the rustup override
    let status = Command::new("rustup")
        .arg("override")
        .arg("unset")
        .arg("--nonexistent")
        .status()
        .expect("Failed to execute rustup override unset");

    if !status.success() {
        eprintln!("rustup override unset failed with status: {}", status);
    }

    // Unset the RUSTC variable
    env::remove_var("RUSTC");
    println!("Unset RUSTC");
}

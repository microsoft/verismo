use std::env;
use std::fs::File;
use std::io::Write;
use std::process::Command;

fn main() {
    // Environment vars during build.
    if cfg!(feature = "noverify") {
        println!("cargo:rustc-env=VERUS_ARGS=--no-verify");
    } else {
        println!("cargo:rustc-env=VERUS_ARGS=--rlimit=8000 --expand-errors --multiple-errors=5 --triggers-silent --time-expanded --no-auto-recommends-check --output-json");
    }

    let module_path = env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-env=MODULE_PATH={}", module_path);

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MODULE");

    // Post build
    let target_dir = env::var("OUT_DIR").unwrap();
    let work_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let executable_path = format!("{}/../../../verismo_main", target_dir); // Adjust the path if necessary
    let igvmgen = work_dir.clone() + "/../../tools/igvm/igvm/igvmgen.py";
    let bzimage = work_dir.clone() + "../../richos/target/bzImage";
    let igvmscript_path = format!("{}/../../../igvm.sh", target_dir);
    println!("cargo:rerun-if-changed={}", igvmgen);
    let igvmout = format!("{}/../../../verismo-rust.bin", target_dir);
    let mut cmd = Command::new("python3");
    cmd.arg(igvmgen);
    cmd.args(["-k", &executable_path]);
    cmd.args(["-o", &igvmout]);
    cmd.args([
        "-vtl=2",
        "-append",
        "root=/dev/sda rw debugpat",
        "-inform",
        "verismo",
        "-boot_mode",
        "x64",
        "-pgtable_level",
        "4",
        "-vmpl2_kernel",
        &bzimage,
    ]);

    let cmd_str = format!("{:?}", cmd);

    // Write the command to a shell script file
    let mut file = File::create(igvmscript_path.clone()).expect("Failed to create file");
    writeln!(file, "#!/bin/sh").expect("Failed to write to file");
    writeln!(file, "{}", cmd_str).expect("Failed to write to file");

    // Make the script executable
    Command::new("chmod")
        .arg("+x")
        .arg(igvmscript_path)
        .status()
        .expect("Failed to change file permissions");
}

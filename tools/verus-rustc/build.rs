use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, ExitStatus};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=install-verus.sh");
    println!("rerun-if-env-changed=HOME");
    println!("rerun-if-env-changed=VERUS_PATH");
    println!("rerun-if-env-changed=CARGO_HOME");
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let cargo_home_dir =
        env::var("CARGO_HOME").map_or(PathBuf::from("/usr/local"), |v| PathBuf::from(v));
    // Construct the path to the dependency's source code
    let verus_dir = env::var("VERUS_PATH")
        .map_or(cargo_home_dir.join("git/checkouts/verus"), |v| {
            PathBuf::from(v)
        });
    let is_install = env::var("DEBUG").unwrap() == "false";
    println!("{:#?}", env::vars());
    let install_dir = if is_install {
        env::var("CARGO_INSTALL_ROOT").map_or(cargo_home_dir.join("bin"), |v| PathBuf::from(v))
    } else {
        out_dir
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf()
    };
    if !install_dir.exists() {
        panic!("{:#?}", install_dir);
    }

    println!("Building verus...");

    // Check if the directory exists
    if verus_dir.exists() {
        println!("{:#?} already exists. Pulling latest changes...", verus_dir);
        let status = Command::new("git")
            .arg("pull")
            .current_dir(&verus_dir)
            .status()
            .expect("Failed to pull latest changes");
        check_status(status);
    } else {
        let repo_url = "https://github.com/verus-lang/verus";
        println!(
            "{:#?} does not exist. Cloning the repository...",
            &verus_dir
        );
        let status = Command::new("git")
            .arg("clone")
            .arg(repo_url)
            .arg(&verus_dir)
            .status()
            .expect("Failed to clone the repository");
        check_status(status);
    }

    let verus_rust_toolchain = verus_dir.join("rust-toolchain.toml");

    // Read the rust-toolchain.toml file
    let toolchain_content =
        fs::read_to_string(&verus_rust_toolchain).expect("Failed to read rust-toolchain.toml");

    // Check and update the toolchain version
    if toolchain_content.contains(r#"channel = "1.76.0""#) {
        let updated_content = toolchain_content.replace("1.76.0", "nightly-2023-12-22");
        fs::write(&verus_rust_toolchain, updated_content)
            .expect("Failed to update rust-toolchain.toml");
    } else if !toolchain_content.contains(r#"channel = "nightly-2023-12-22""#) {
        panic!("rust toolchain version != 1.76. Please update the script");
    }

    // Run additional commands in the verus directory
    if !verus_dir.join("source/z3").exists() {
        let status = Command::new("tools/get-z3.sh")
            .current_dir(&verus_dir.join("source"))
            .status()
            .expect("Failed to run get-z3.sh");
        check_status(status);
    }

    // Activate the environment and build
    let env_path = std::env::var("PATH").unwrap();
    let status = Command::new("bash")
        .env_clear()
        .env("PATH", env_path)
        .arg("-c")
        .arg("source ../tools/activate && vargo build --release")
        .current_dir(&verus_dir.join("source"))
        .status()
        .expect("Failed to build verus");
    check_status(status);

    // Copy the built binaries to the install directory
    for binary in [
        "verus",
        "rust_verify",
        "z3",
        "verus-root",
        "libvstd.rlib",
        "vstd.vir",
        "libstate_machines_macros.so",
        "libbuiltin_macros.so",
        "libbuiltin.rlib",
    ]
    .iter()
    {
        let src = verus_dir.join("source/target-verus/release").join(binary);
        let dest = install_dir.join(binary);
        if !src.exists() {
            panic!("{:#?} not exists", src);
        }
        println!("copy {:#?} to {:#?}", src, dest);
        fs::copy(&src, &dest).expect("Failed to copy binary");
    }

    // Install verusfmt
    println!("Installing verusfmt...");
    let status = Command::new("cargo")
        .arg("install")
        .arg("--git")
        .arg("https://github.com/verus-lang/verusfmt")
        .status()
        .expect("Failed to install verusfmt");
    check_status(status);
}

fn check_status(status: ExitStatus) {
    if !status.success() {
        panic!("Command failed with status: {}", status);
    }
}

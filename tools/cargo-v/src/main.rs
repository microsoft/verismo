use signal_hook::consts::SIGINT;
use signal_hook::consts::SIGTERM;
use signal_hook::iterator::Signals;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::PathBuf;
use std::process::{exit, Command};

fn check_status(status: std::process::ExitStatus) {
    if !status.success() {
        panic!("{}", status);
    }
}

fn main() {
    // Install and activate
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        panic!("use `cargo-v -- $cmd ...` or `cargo v $cmd ...`");
    }

    let args = &args[2..];
    match args[0].as_str() {
        "enable" => {
            activate();
        }
        "disable" => {
            deactivate();
        }
        "build" => {
            build(&args);
        }
        "install-verus" => {
            install();
        }
        _ => {
            panic!("{} not implemented", args[0]);
        }
    }
}

fn build(args: &[String]) {
    // Set up signal handling
    let verus_arg = args.iter().position(|arg| arg == "--verus");
    let verus_path = verus_arg.map_or(
        get_verus_path().0.map_or(PathBuf::from("verus"), |p| {
            p.join("source/target-verus/release/verus").to_path_buf()
        }),
        |i| PathBuf::from(&args[i + 1]),
    );
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
        .args(args)
        .env("VERUS", verus_path)
        .env("RUSTC", "verus-rustc")
        .status()
        .expect("Failed to execute cargo build");

    if !status.success() {
        eprintln!("cargo build failed with status: {}", status);
    }
    deactivate();
}

fn get_verus_path() -> (Option<PathBuf>, String, String) {
    let output = Command::new("cargo")
        .arg("tree")
        .output()
        .expect("Failed to execute cargo tree");

    let out = String::from_utf8_lossy(&output.stdout);
    let grep = out.lines().find(|line| line.contains("builtin_macros"));
    let path = grep
        .map(|line| {
            line.split("(proc-macro) (")
                .nth(1)
                .and_then(|s| s.split(")").nth(0))
                .unwrap()
        })
        .unwrap();
    let verus_rev = grep
        .map(|line| {
            line.split("rev=")
                .nth(1)
                .and_then(|s| s.split('#').next())
                .unwrap_or("")
        })
        .unwrap_or("");

    let url = grep
        .map(|line| {
            line.split("https:")
                .nth(1)
                .and_then(|s| s.split('?').nth(0))
                .unwrap_or("")
        })
        .unwrap_or("//github.com/verus-lang/verus");
    let url = "https:".to_string() + url;
    let path = PathBuf::from(path);
    let path = if path.exists() {
        Some(path.parent().unwrap().parent().unwrap().to_path_buf())
    } else {
        None
    };
    (path, url, verus_rev.to_string())
}

fn install() {
    // Get the verus revision
    let (path, url, verus_rev) = get_verus_path();

    println!("Using verus commit {} {} {:?}", url, verus_rev, path);
    install_verus(url.as_str(), verus_rev.as_str(), path);

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
}

fn install_verus(repo_url: &str, verus_rev: &str, path: Option<PathBuf>) {
    let cargo_home_dir = env::var("CARGO_HOME").map_or(
        PathBuf::from(format!("{}/.cargo/", env::var("HOME").unwrap())),
        |v| PathBuf::from(v),
    );
    // Construct the path to the dependency's source code
    let verus_dir = if path.is_some() {
        path.unwrap()
    } else {
        env::var("VERUS_PATH").map_or(
            cargo_home_dir.join(&format!("git/checkouts/verus-{}", verus_rev)),
            |v| PathBuf::from(v),
        )
    };
    let rust_version = env::var("VERUS_RUST_VERSION").unwrap_or("nightly-2023-12-22".into());

    let install_dir =
        env::var("CARGO_INSTALL_ROOT").map_or(cargo_home_dir.join("bin"), |v| PathBuf::from(v));

    if !install_dir.exists() {
        panic!("{:#?} does not exist", install_dir);
    }

    println!("Building verus...");
    let zip = format!("{}.zip", verus_rev);

    // Check if the directory exists
    if verus_dir.exists() {
        println!("{:#?} already exists.", verus_dir);
    } else {
        println!(
            "{:#?} does not exist. Cloning the repository...",
            &verus_dir
        );
        let status = Command::new("wget")
            .arg(&format! {"{}/archive/{}", repo_url, zip})
            .status()
            .expect("Failed to clone the repository");
        check_status(status);
        let status = Command::new("unzip")
            .arg("-q")
            .arg(zip.clone())
            .arg("-d")
            .arg(verus_dir.parent().unwrap())
            .status()
            .expect("Failed to unzip the file");
        check_status(status);
        let _ = fs::remove_file(zip);
    }

    let verus_rust_toolchain = verus_dir.join("rust-toolchain.toml");

    // Read the rust-toolchain.toml file
    let toolchain_content =
        fs::read_to_string(&verus_rust_toolchain).expect("Failed to read rust-toolchain.toml");
    // Check and update the toolchain version
    let mut toolconfig: toml::Value =
        toml::de::from_str::<toml::Value>(toolchain_content.as_str()).unwrap();
    *toolconfig
        .get_mut("toolchain")
        .unwrap()
        .get_mut("channel")
        .unwrap() = rust_version.into();
    let _ = fs::write(
        &verus_rust_toolchain,
        toml::ser::to_string(&toolconfig).unwrap(),
    );
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

use cargo_metadata::CargoOpt;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

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
    let verus_meta = VerusMetadata::new(args);
    match args[0].as_str() {
        "build" => {
            build(&verus_meta, args);
        }
        "prepare-verus" => {
            install(&verus_meta, false);
        }
        "install-verus" => {
            install(&verus_meta, true);
        }
        "enable" => {
            println("use cargo-v -- build directly.");
            activate();
        }
        "disable" => {
            deactivate();
        }
        _ => {
            panic!("{} not implemented", args[0]);
        }
    }
}

fn show_rust_version() {
    let _ = Command::new("rustup")
        .arg("override")
        .arg("list")
        .status()
        .expect("Failed to execute command");
    let _ = Command::new("rustup")
        .arg("show")
        .arg("active-toolchain")
        .status()
        .expect("Failed to execute command");
}

fn rust_version() -> String {
    env::var("VERUS_RUST_VERSION").unwrap_or("nightly-2023-12-22".into())
}

fn build(verus_meta: &VerusMetadata, args: &[String]) {
    let verus = verus_meta.verus();
    let verus_crates = verus_meta.find_verus_crates();
    // Run cargo build with additional arguments
    let status = Command::new("cargo")
        .args(args)
        .env("VERUS", verus)
        .env("RUSTC", "verus-rustc")
        .env("RUSTUP_TOOLCHAIN", rust_version())
        .env("VERUS_TARGETS", verus_crates.join(","))
        .status()
        .expect("Failed to execute cargo build");

    if !status.success() {
        eprintln!("cargo build failed with status: {}", status);
    }
}

fn install(verus_meta: &VerusMetadata, global: bool) {
    // Get the verus revision
    install_verus(verus_meta, global);

    let status = Command::new("cargo")
        .arg("install")
        .arg("--git")
        .arg("https://github.com/microsoft/verismo/")
        .arg("verus-rustc")
        .status()
        .expect("Failed to execute cargo install");

    if !status.success() {
        eprintln!("cargo install failed with status: {}", status);
    }
}

fn activate() {
    let rust_version = rust_version();
    // Set the rustup override and RUSTC variable
    let status = Command::new("rustup")
        .arg("override")
        .arg("set")
        .arg(rust_version)
        .status()
        .expect("Failed to execute rustup override");

    if !status.success() {
        eprintln!("rustup override set failed with status: {}", status);
    }
    show_rust_version();
}

fn deactivate() {
    let status = Command::new("rustup")
        .arg("override")
        .arg("unset")
        .arg("--path")
        .arg(env::current_dir().expect("no current dir"))
        .status()
        .expect("Failed to execute rustup override unset");
    if !status.success() {
        eprintln!("rustup override unset failed with status: {}", status);
    }
}

fn extract_features(args: &[String]) -> Vec<String> {
    let mut extracted_features = Vec::new();

    let mut i = 0;
    while i < args.len() {
        if args[i] == "--features" {
            // Check the next argument
            i += 1;
            extracted_features.push(args[i].clone());
        }
        i += 1; // Move to the next argument
    }

    extracted_features
}

struct VerusMetadata {
    meta: cargo_metadata::Metadata,
    verus_path: Option<PathBuf>,
}

impl VerusMetadata {
    fn new(args: &[String]) -> VerusMetadata {
        let features = extract_features(args);
        let mut ret = VerusMetadata {
            meta: cargo_metadata::MetadataCommand::new()
                .features(CargoOpt::SomeFeatures(features))
                .exec()
                .expect("failed to get metadata"),
            verus_path: None,
        };
        ret.verus_path = ret.find_verus_dir();
        ret
    }

    fn verus_dir(&self) -> PathBuf {
        env::var("VERUS_PATH").map_or(
            self.verus_path.clone().unwrap_or(PathBuf::from("verus")),
            PathBuf::from,
        )
    }

    fn verus(&self) -> PathBuf {
        let ret = env::var("VERUS").map_or(
            self.verus_path
                .clone()
                .expect("need to init VerusMetadata")
                .join("source/target-verus/release/verus"),
            PathBuf::from,
        );
        if !ret.exists() {
            panic!(
                "Please run `cargo v install-verus` to build verus first at {:?}",
                ret
            )
        }
        ret
    }

    fn find_verus_crates(&self) -> Vec<String> {
        let mut ret = vec![];
        for p in &self.meta.packages {
            for d in &p.dependencies {
                if d.name == "builtin"
                    && d.source
                        .as_ref()
                        .expect("builtin should have source")
                        .contains("verus")
                {
                    ret.push(p.name.clone());
                    break;
                }
            }
        }
        ret
    }

    fn find_verus_dir(&self) -> Option<PathBuf> {
        self.find_src_dir("builtin")
    }

    fn find_src_dir(&self, c: &str) -> Option<PathBuf> {
        for p in &self.meta.packages {
            if p.name.as_str() == c {
                for t in &p.targets {
                    let builtin_path = PathBuf::from(t.src_path.as_str());
                    if builtin_path.exists() {
                        return Some(
                            builtin_path
                                .parent()
                                .unwrap()
                                .parent()
                                .unwrap()
                                .parent()
                                .unwrap()
                                .parent()
                                .unwrap()
                                .to_path_buf(),
                        );
                    }
                }
            }
        }
        None
    }
}

fn install_verus(verus_meta: &VerusMetadata, install: bool) {
    // Construct the path to the dependency's source code
    let verus_dir = verus_meta.verus_dir();
    let rust_version = env::var("VERUS_RUST_VERSION").unwrap_or("nightly-2023-12-22".into());

    println!("Building verus...");

    // Check if the directory exists
    if verus_dir.exists() {
        println!("{:#?} already exists.", verus_dir);
    } else {
        panic!(
            "{:#?} does not exist. Please put builtin in Cargo.toml or download verus to $VERUS_PATH",
            &verus_dir
        );
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
            .current_dir(verus_dir.join("source"))
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
        .arg(
            "source ../tools/activate && vargo build --release --vstd-no-verify --vstd-no-verusfmt",
        )
        .current_dir(verus_dir.join("source"))
        .status()
        .expect("Failed to build verus");
    check_status(status);
    if install {
        let cargo_home_dir = env::var("CARGO_HOME").map_or(
            PathBuf::from(format!("{}/.cargo/", env::var("HOME").unwrap())),
            PathBuf::from,
        );
        let install_dir =
            env::var("CARGO_INSTALL_ROOT").map_or(cargo_home_dir.join("bin"), PathBuf::from);

        if !install_dir.exists() {
            panic!("{:#?} does not exist", install_dir);
        }
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
    }
}

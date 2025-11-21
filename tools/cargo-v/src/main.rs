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

const VERUS_CORE_LIBS: [&str; 7] = [
    "vstd",
    "builtin_macros",
    "builtin",
    "state_machines_macros",
    "verus_builtin_macros",
    "verus_builtin",
    "verus_state_machines_macros",
];

const VERUS_BINS: [&str; 12] = [
    "verus",
    "rust_verify",
    "z3",
    "verus-root",
    "libvstd.rlib",
    "vstd.vir",
    "libverus_state_machines_macros.so",
    "libverus_builtin_macros.so",
    "libverus_builtin.rlib",
    "libstate_machines_macros.so",
    "libbuiltin_macros.so",
    "libbuiltin.rlib",
];

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
            install_verus(&verus_meta, false);
        }
        "install-verus" => {
            install_verus(&verus_meta, true);
        }
        _ => {
            build(&verus_meta, args);
        }
    }
}

fn build(verus_meta: &VerusMetadata, args: &[String]) {
    let verus = verus_meta.verus();
    let verus_crates = verus_meta.find_verus_crates();
    if let Some(lib_version) = verus_meta.use_prebuilt() {
        let (verus_version, _) = verus_meta.verus_version();
        if !verus_version.contains(&lib_version) {
            panic!("Prebuilt verus tool version {} is too far away from the verus lib version {}x specified in Cargo.toml. Please run `cargo v install-verus` to update the prebuilt verus.", verus_version, lib_version);
        }
    }
    // Run cargo build with additional arguments
    let mut cmd = Command::new("cargo");
    let cmd = cmd
        .args(args)
        .env("VERUS", verus)
        .env("RUSTC", "verus-rustc")
        .env("RUSTUP_TOOLCHAIN", verus_meta.rust_version())
        .env("VERUS_TARGETS", verus_crates.join(","));
    println!("{:?}", cmd);
    let status = cmd.status().expect("Failed to execute cargo build");

    if !status.success() {
        eprintln!("cargo build failed with status: {}", status);
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
    rust_version: Option<String>,
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
            rust_version: None,
        };
        ret.verus_path = ret.find_verus_dir();
        ret.rust_version = ret.set_rust_version();
        ret
    }

    fn verus_dir(&self) -> PathBuf {
        env::var("VERUS_PATH").map_or(
            self.verus_path.clone().unwrap_or(PathBuf::from("verus")),
            PathBuf::from,
        )
    }

    fn rust_version(&self) -> String {
        self.rust_version.clone().unwrap_or(self.verus_version().1)
    }

    fn verus_version(&self) -> (String, String) {
        let output = Command::new(self.verus())
            .arg("--version")
            .output()
            .expect("Failed to execute verus to get version");
        if output.status.code().unwrap() != 0 {
            panic!(
                "Failed to get verus version({}): {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let version_str = String::from_utf8_lossy(&output.stdout);
        let version_parts: Vec<&str> = version_str.split("Version: ").collect();
        let version = version_parts[1].split_whitespace().next().unwrap();
        let rust_version_parts: Vec<&str> = version_str.split("Toolchain: ").collect();
        let rust_version = rust_version_parts[1].split("-").next().unwrap();
        return (version.to_string(), rust_version.to_string());
    }

    fn set_rust_version(&self) -> Option<String> {
        if self.use_prebuilt().is_some() {
            // get version via `verus --version`
            return None;
        }
        let verus_rust_toolchain = self.verus_dir().join("rust-toolchain.toml");

        // Read the rust-toolchain.toml file
        let toolchain_content =
            fs::read_to_string(&verus_rust_toolchain).expect("Failed to read rust-toolchain.toml");
        // Check and update the toolchain version
        let mut toolconfig: toml::Value =
            toml::de::from_str::<toml::Value>(toolchain_content.as_str()).unwrap();
        let customized_version = env::var("VERUS_RUST_VERSION");
        let v = match customized_version {
            Ok(v) => {
                *toolconfig
                    .get_mut("toolchain")
                    .unwrap()
                    .get_mut("channel")
                    .unwrap() = v.clone().into();
                let _ = fs::write(
                    &verus_rust_toolchain,
                    toml::ser::to_string(&toolconfig).unwrap(),
                );
                v
            }
            _ => toolconfig
                .get("toolchain")
                .unwrap()
                .get("channel")
                .unwrap()
                .to_string()
                .replace("\"", "")
                .replace("'", ""),
        };
        Some(v)
    }

    fn verus(&self) -> PathBuf {
        let ret = env::var("VERUS").map_or(
            if self.use_prebuilt().is_some() {
                // which verus path
                let output = Command::new("which")
                    .arg("verus")
                    .output()
                    .expect("Failed to execute which verus");
                let verus_path =
                    String::from_utf8(output.stdout).expect("Failed to parse curl output as UTF-8");
                PathBuf::from(verus_path.trim())
            } else {
                self.verus_path
                    .clone()
                    .expect("need to init VerusMetadata")
                    .join("source/target-verus/release/verus")
            },
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
                if VERUS_CORE_LIBS.contains(&d.name.as_str()) {
                    ret.push(p.name.clone());
                    break;
                }
            }
        }
        ret
    }

    fn use_prebuilt(&self) -> Option<String> {
        let mut year_month_days = vec![];
        for p in &self.meta.packages {
            let pname = p.name.as_str();
            if VERUS_CORE_LIBS.contains(&pname) {
                for t in &p.targets {
                    let builtin_path = PathBuf::from(t.src_path.as_str());
                    let path_str = builtin_path.as_os_str().to_str().unwrap();
                    if path_str.contains("index.crates.io") {
                        let version_parts: Vec<&str> = path_str.split(pname).collect();
                        // -0.0.0-year-month-date-
                        let version = version_parts[1].split("/").nth(0).unwrap();
                        let version_parts = version.split("-").collect::<Vec<&str>>();
                        let year = version_parts[2];
                        let month = version_parts[3];
                        let day = version_parts[4][0..1].to_string();
                        year_month_days.push((year.to_string(), month.to_string(), day));
                    }
                }
            }
        }
        if year_month_days.is_empty() {
            return None;
        }
        year_month_days.sort();
        Some(
            year_month_days
                .last()
                .map(|(y, m, d)| format!("0.{y}.{m}.{d}"))
                .unwrap(),
        )
    }

    fn find_verus_dir(&self) -> Option<PathBuf> {
        for p in &self.meta.packages {
            if VERUS_CORE_LIBS.contains(&p.name.as_str()) {
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
    let (tmp_dir, verus_bin_dir) = if let Some(version) = verus_meta.use_prebuilt() {
        let repo = "verus-lang/verus";
        let os = std::env::consts::OS;
        let arch = std::env::consts::ARCH;
        let arch = match arch {
            "x86_64" => "x86",
            "aarch64" => "arm64",
            "arm64" => "arm64",
            _ => {
                panic!("Prebuilt verus is not available for architecture: {}", arch);
            }
        };
        let arch_os = format!("{arch}-{os}");
        let verus_bin_dir = format!("verus-{}", arch_os);
        let tmp_dir = format!("tmp-{}", version);
        let verus_zip = format!("{}.zip", verus_bin_dir);
        let output = Command::new("curl")
            .args(&[
                "-s",
                &format!("https://api.github.com/repos/{}/releases", repo),
                "-H",
                "User-Agent: rust-curl-script",
            ])
            .output()
            .expect("Failed to execute curl to get releases");
        let body = String::from_utf8(output.stdout).expect("Failed to parse curl output as UTF-8");
        let download_url = body
            .lines()
            .find(|line| {
                line.contains(&version)
                    && line.contains(&arch_os)
                    && line.contains("browser_download_url")
            })
            .and_then(|line| {
                // Extract the JSON value of tag_name
                let start = line
                    .find(": \"")
                    .expect("Failed to find start of download URL")
                    + 3;
                let end = line[start..]
                    .find('"')
                    .expect("Failed to find end of download URL")
                    + start;
                Some(&line[start..end])
            })
            .expect(&format!("Release not found for {}", version));
        println!("Downloading verus from {}", download_url);
        Command::new("curl")
            .args(&["-L", "-o", &verus_zip, &download_url])
            .status()
            .expect("Failed to execute curl to download verus");
        Command::new("unzip")
            .args(&[&verus_zip, "-d", &tmp_dir])
            .status()
            .expect("Failed to execute unzip to extract verus");
        Command::new("rm")
            .arg(&verus_zip)
            .status()
            .expect("Failed to remove verus zip file");
        (
            Some(tmp_dir.clone()),
            PathBuf::from(&tmp_dir).join(&verus_bin_dir),
        )
    } else {
        let verus_dir = verus_meta.verus_dir();

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
            "source ../tools/activate && vargo build --release --vstd-no-verify --vstd-no-verusfmt && rm -rf target-verus/release/*/*.toml",
        )
        .current_dir(verus_dir.join("source"))
        .status()
        .expect("Failed to build verus");
        check_status(status);
        (None, verus_dir.join("source/target-verus/release"))
    };
    if install {
        println!("Installing verus binaries...");
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
        for binary in VERUS_BINS {
            let src = verus_bin_dir.join(binary);
            let dest = install_dir.join(binary);
            if !src.exists() {
                continue;
            }
            println!("install {:#?}", dest);
            fs::copy(&src, &dest).expect("Failed to copy binary");
        }
        if let Some(tmp_dir) = &tmp_dir {
            // make executable
            Command::new("rm")
                .args(&["-rf", tmp_dir])
                .status()
                .expect("Failed to remove verus zip file");
        }
    }
}

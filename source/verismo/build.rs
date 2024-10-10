use std::collections::HashSet;
use std::env;
use std::path::PathBuf;

fn main() {
    // Environment vars during build.
    if let Ok(module_name) = env::var("VERUS_MODULE") {
        let module_path = env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
        let modules_args = process_module(&module_path, &module_name);
        println!(
            "cargo:rustc-env={}_VERUS_ARGS={}",
            env::var("CARGO_PKG_NAME").unwrap(),
            modules_args.join(" ")
        );
    }
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MODULE");
    println!("cargo:rerun-if-env-changed=verismo_VERUS_ARGS");
    init_verify(&["vstd"]);
}

#[inline]
pub fn init_verify(verus_libs: &[&str]) {
    if cfg!(feature = "noverify") {
        println!("cargo:rustc-env=VERUS_ARGS=--no-verify");
    } else {
        let verus_args = [
            "--rlimit=8000",
            "--expand-errors",
            "--multiple-errors=5",
            "--triggers-silent",
            "--no-auto-recommends-check",
            "--trace",
            "-Z unstable-options",
        ];
        println!("cargo:rustc-env=VERUS_ARGS={}", verus_args.join(" "));
    }

    let target = std::env::var("CARGO_PKG_NAME").unwrap_or_default();
    let mut targets: Vec<&str> = vec![&target];
    targets.extend(verus_libs);
    println!("cargo:rustc-env=VERUS_TARGETS={}", targets.join(","));
    for (key, value) in std::env::vars() {
        // You can filter or modify which ones to pass to rustc
        println!("cargo:rustc-env={}={}", key, value);
    }

    let module_path = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-env=MODULE_PATH={}", module_path);
}

fn find_rs_files(path: &PathBuf) -> Vec<String> {
    let mut files = Vec::new();
    if path.exists() {
        for entry in std::fs::read_dir(path).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() && path.extension().unwrap_or_default() == "rs" {
                files.push(path.to_string_lossy().into_owned());
            } else if path.is_dir() {
                files.extend(find_rs_files(&path))
            }
        }
    } else {
        panic!("{:?} does not exit", path)
    }
    files
}

fn process_module(verismo_path: &str, module_name: &str) -> Vec<String> {
    let dir = PathBuf::from(verismo_path).join("src");
    let module_files = find_rs_files(&dir);

    let prefix = dir.into_os_string().into_string().unwrap();

    let modules = module_files
        .iter()
        .map(|path| {
            path.to_string()
                .strip_prefix(&prefix)
                .unwrap()
                .to_string()
                .replace("/lib.rs", "")
                .replace("/main.rs", "")
                .replace("/mod.rs", "")
                .replace("/", "::")
                .replace(".rs", "")
        })
        .map(|path| path.strip_prefix("::").unwrap_or(&path).to_string())
        .collect::<HashSet<_>>();
    let mut ret = vec![];
    for m in &modules {
        if m.starts_with(&format!("{}::", module_name)) || m == module_name {
            ret.push("--verify-module".to_string());
            ret.push(m.to_string());
        }
    }
    ret
}

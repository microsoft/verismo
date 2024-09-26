use log::{debug, LevelFilter};
use log4rs::append::file::FileAppender;
use log4rs::config::{Appender, Config, Root};
use log4rs::encode::pattern::PatternEncoder;
use std::collections::HashSet;
use std::env;
use std::fs::File;
use std::path::Path;
use std::process::{exit, Command};

fn find_rs_files(path: &Path) -> Vec<String> {
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
        debug!("{:?} does not exit", path)
    }
    files
}

fn process_module(verismo_path: &str, module_name: &str) -> Vec<String> {
    let dir = Path::new(verismo_path).join("src");
    let module_files = find_rs_files(&dir);

    let prefix = dir.into_os_string().into_string().unwrap();
    debug!("module_files: {:?}", module_files);

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
    debug!("modules: {:?}", modules);
    let mut ret = vec![];
    for m in &modules {
        if m.starts_with(&format!("{}::", module_name)) || m == module_name {
            ret.push("--verify-module".to_string());
            ret.push(m.to_string());
        }
    }
    debug!("Processed modules({}): {:?}", module_name, ret);
    ret
}

fn get_value(args: &[String], param: &str) -> Option<String> {
    let mut iter = args.iter();
    while let Some(item) = iter.next() {
        if item == param {
            return iter.next().map(|s| s.to_string());
        }
    }
    None
}
fn main() -> std::io::Result<()> {
    let logfile = FileAppender::builder()
        .encoder(Box::new(PatternEncoder::new("{l} - {m}\n")))
        .build("verismo_log.log")
        .unwrap();

    let config = Config::builder()
        .appender(Appender::builder().build("logfile", Box::new(logfile)))
        .build(
            Root::builder()
                .appender("logfile")
                .build(LevelFilter::Debug),
        )
        .unwrap();

    log4rs::init_config(config).unwrap();

    let main_target = env::var("CARGO_PKG_NAME").unwrap_or_default();
    // crate1,crate2,..
    let verus_target_str = env::var("VERUS_TARGETS").unwrap_or_default();
    let verus_targets: Vec<&str> = verus_target_str.split(',').collect();
    let script = env::current_exe()?;
    let script_dir = script.parent().unwrap();
    let top_dir = script_dir.parent().unwrap();
    let verus_snp_dir = top_dir;

    let verus_args = env::var("VERUS_ARGS").unwrap_or_default(); //[String]
    let verifier_path = env::var("VERUS_PATH").unwrap_or_default();
    let _z3_path = env::var("Z3_PATH").unwrap_or_else(|_| "/usr/bin/z3".to_string());

    let mut verus_args: Vec<String> = verus_args
        .split_whitespace()
        .map(|s| s.to_string())
        .collect();

    let mut module_verus_args: Vec<String> = vec![];
    if let Ok(module_name) = env::var("VERUS_MODULE") {
        let module_path = env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
        let modules = process_module(&module_path, &module_name);
        module_verus_args.extend(modules);
    } else {
        debug!("No module name provided.");
    }

    debug!("verus_args: {:?}", verus_args);
    let mut args: Vec<String> = env::args().skip(1).collect();

    let _arch = match env::consts::ARCH {
        "x86_64" => "x86_64",
        "aarch64" => "aarch64",
        _ => {
            debug!("Unknown architecture {}", env::consts::ARCH);
            exit(1);
        }
    };

    let ld_library_path = env::var("LD_LIBRARY_PATH").unwrap_or_default()
        + &format!(
            ":{}/source/target/release/deps",
            verus_snp_dir.to_string_lossy()
        );
    env::set_var("LD_LIBRARY_PATH", &ld_library_path);

    let _cmd_log = File::create("cmd.log")?;

    let rust_flags = env::var("RUSTFLAGS").unwrap_or_default();
    let rust_flags_verus_lib = format!(
        "{} --cfg proc_macro_span --cfg verus_keep_ghost ",
        rust_flags
    );
    let verus_lib_cfg = [
        "--cfg".to_string(),
        "proc_macro_span".to_string(),
        "--cfg".to_string(),
        "verus_keep_ghost".to_string(),
    ];
    let crate_name = get_value(&args, "--crate-name");
    if let Some(crate_name) = crate_name {
        if verus_targets.contains(&crate_name.as_str()) {
            if main_target == crate_name {
                // only do module-level verification for the target crate.
                verus_args.extend(module_verus_args);
            }
            let extra_str = env::var(format!("{}_VERUS_ARGS", crate_name)).unwrap_or_default();
            let extra: Vec<&str> = if !extra_str.is_empty() {
                extra_str.split(" ").collect()
            } else {
                vec![]
            };
            let extra: Vec<String> = extra.iter().map(|s| s.to_string()).collect();
            verus_args.extend(extra);
            run_verus_verify(&verifier_path, &args, &verus_args, &rust_flags, true)?;
        } else if crate_name == "vstd" {
            args.extend(verus_lib_cfg);
            run_verus_verify(
                &verifier_path,
                &args,
                &[
                    "--no-vstd".to_string(),
                    "--no-verify".to_string(),
                    "--no-builtin".to_string(),
                ],
                &rust_flags_verus_lib,
                true,
            )?;
        } else {
            args.extend(verus_lib_cfg);
            run_rustc(&args, &rust_flags_verus_lib)?;
        }
    } else {
        args.extend(verus_lib_cfg);
        run_rustc(&args, &rust_flags_verus_lib)?;
    }

    Ok(())
}

fn run_verus_verify(
    verifier_path: &str,
    args: &[String],
    verus_args: &[String],
    rust_flags: &str,
    compile: bool,
) -> std::io::Result<()> {
    let mut command = Command::new(verifier_path);
    let mut combined_args = args.to_vec();
    combined_args.extend_from_slice(verus_args);
    command.args(combined_args);
    command.env("RUSTFLAGS", rust_flags);
    command.env(
        "LD_LIBRARY_PATH",
        env::var("LD_LIBRARY_PATH").unwrap_or_default(),
    );

    if compile {
        command.arg("--compile");
    }

    debug!("cmd: {:?}", command);

    // Wait for the command to finish and get its status
    let status = command.status()?;
    if !status.success() {
        exit(status.code().unwrap_or(1));
    }

    Ok(())
}

fn run_rustc(args: &[String], rust_flags: &str) -> std::io::Result<()> {
    let mut command = Command::new("rustc");
    command.args(args);
    command.env("RUSTFLAGS", rust_flags);
    command.env(
        "LD_LIBRARY_PATH",
        env::var("LD_LIBRARY_PATH").unwrap_or_default(),
    );
    debug!("cmd: {:?}", command);
    let status = command.status()?;
    if !status.success() {
        exit(status.code().unwrap_or(1));
    }

    Ok(())
}

use log::{debug, LevelFilter};
use log4rs::append::file::FileAppender;
use log4rs::config::{Appender, Config, Root};
use log4rs::encode::pattern::PatternEncoder;
use std::env;
use std::process::{exit, Command};

fn get_value(args: &[String], param: &str) -> Option<String> {
    let mut iter = args.iter();
    while let Some(item) = iter.next() {
        if item == param {
            return iter.next().map(|s| s.to_string());
        }
    }
    None
}

fn update_imports_exports(
    crate_name: &str,
    args: &[String],
    verus_targets: &[String],
) -> Vec<String> {
    let mut iter = args.iter();
    let mut more_args = vec![];
    let out_dir = get_value(args, "--out-dir").unwrap();
    while let Some(item) = iter.next() {
        if item == "--extern" {
            let val = iter.next().unwrap().to_string();
            if let Some(name) = val.split("=").next() {
                if verus_targets.contains(&name.to_string()) {
                    debug!("import {}", name);
                    more_args.extend([
                        "--import".to_string(),
                        val.replace(".rmeta", ".vir").replace(".rlib", ".vir"),
                    ]);
                }
            }
        } else if item == "-C" {
            let val = iter.next().unwrap().to_string();
            if val.starts_with("metadata=") {
                let extra = val.replace("metadata=", "");
                more_args.extend([
                    "--export".to_string(),
                    format!("{}/lib{}-{}.vir", out_dir, crate_name, extra).to_string(),
                ]);
            }
        }
    }
    more_args
}
fn main() -> std::io::Result<()> {
    let logfile = FileAppender::builder()
        .encoder(Box::new(PatternEncoder::new("{l} - {m}\n")))
        .build("verus_rustc.log")
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
    // crate1,crate2,..
    let verus_target_str = env::var("VERUS_TARGETS").unwrap_or_default();

    let verus_targets: Vec<String> = verus_target_str
        .split(',')
        .map(|c| c.replace("-", "_"))
        .collect();
    let script = env::current_exe()?;
    let script_dir = script.parent().unwrap();
    let top_dir = script_dir.parent().unwrap();
    let verus_snp_dir = top_dir;

    let verus_args = env::var("VERUS_ARGS").unwrap_or_default(); //[String]
    let verus = env::var("VERUS").unwrap_or("verus".to_string());

    let mut verus_args: Vec<String> = verus_args
        .split_whitespace()
        .map(|s| s.to_string())
        .collect();

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

    let rust_flags = env::var("RUSTFLAGS").unwrap_or_default();
    let rust_flags_verus_lib =
        format!("{} --cfg verus_keep_ghost --cfg span_locations", rust_flags);
    let verus_lib_cfg = ["--cfg".to_string(), "verus_keep_ghost".to_string()];
    let crate_name = get_value(&args, "--crate-name");
    debug!(
        "verus_targets = {:#?}, crate  = {:#?}",
        verus_targets, crate_name
    );
    if let Some(crate_name) = crate_name {
        if crate_name == "vstd" {
            args.extend(verus_lib_cfg);
            let mut verus_args = vec![
                //"--no-vstd".to_string(),
                "--no-verify".to_string(),
                "--cfg".to_string(),
                "erasure_macro_todo".to_string(),
            ];
            verus_args.extend(update_imports_exports(&crate_name, &args, &[]));
            run_verus_verify(
                &verus,
                &args,
                &verus_args,
                &rust_flags_verus_lib,
                true,
                true,
            )?;
        } else if verus_targets.contains(&crate_name) {
            let mut is_bin = false;
            let mut is_lib = false;
            if let Some(v) = get_value(&args, "--crate-type") {
                is_bin = v.contains("bin");
                is_lib = v.contains("lib");
            }
            let lib_or_bin = if is_lib {
                "lib"
            } else if is_bin {
                "bin"
            } else {
                "unknown"
            }; // bin and lib can share the same name.
            let fname = format!("{}_{}_VERUS_ARGS", crate_name, lib_or_bin);
            let extra_str = env::var(fname).unwrap_or_default();
            let extra: Vec<&str> = if !extra_str.is_empty() {
                extra_str.split(" ").collect()
            } else {
                vec![]
            };
            //verus_args.extend(["--no-vstd".to_string()]);
            let extra: Vec<String> = extra.iter().map(|s| s.to_string()).collect();
            verus_args.extend(extra);
            verus_args.extend(update_imports_exports(&crate_name, &args, &verus_targets));
            args.extend(verus_lib_cfg);
            run_verus_verify(
                &verus,
                &args,
                &verus_args,
                &rust_flags_verus_lib,
                true,
                true,
            )?;
        } else {
            if crate_name == "builtin" || crate_name == "builtin_macros" {
                args.extend(verus_lib_cfg);
            }
            run_rustc(&args, &rust_flags)?;
        }
    } else {
        //args.extend(verus_lib_cfg);
        run_rustc(&args, &rust_flags)?;
    }

    Ok(())
}

fn run_verus_verify(
    verus: &str,
    args: &[String],
    verus_args: &[String],
    rust_flags: &str,
    compile: bool,
    is_internal_test_mode: bool,
) -> std::io::Result<()> {
    let mut command = Command::new(verus);
    let mut combined_args: Vec<String> = Vec::new();
    if is_internal_test_mode {
        combined_args.push("--internal-test-mode".to_string());
    }
    combined_args.extend_from_slice(verus_args);

    for arg in args {
        if arg.starts_with("--edition=") {
            continue;
        }
        combined_args.push(arg.to_string());
    }
    command.args(combined_args);
    command.env("RUSTFLAGS", rust_flags);
    command.env("RUSTC_BOOTSTRAP", "1");
    command.env(
        "LD_LIBRARY_PATH",
        env::var("LD_LIBRARY_PATH").unwrap_or_default(),
    );
    command.env_remove("CARGO_MAKEFLAGS");

    if compile {
        command.arg("--compile");
    }

    debug!("verus cmd: {:?}", command);

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
    command.env("RUSTC_BOOTSTRAP", "1");
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

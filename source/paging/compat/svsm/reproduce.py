#!/usr/bin/env python3
"""Apply the local SVSM integration and run its real kernel host tests."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

PIN = "5ee2b61dfa2612dab27fe000c9e46c5b25d9a8f6"
PACKIT_PIN = "98411fde7ddb76061159b4abbf0487a9adba469b"
FIXTURES = Path(__file__).resolve().parent
PAGING = FIXTURES.parent.parent
FILES = {
    "adapter.rs": "kernel/src/mm/verismo_paging.rs",
    "tests.rs": "kernel/src/mm/verismo_paging_tests.rs",
}


def run(*args, cwd, **kwargs):
    return subprocess.run(args, cwd=cwd, check=True, **kwargs)


def check_installed(checkout, patch, parser):
    staged = run("git", "diff", "--cached", "--name-only", cwd=checkout,
                 capture_output=True, text=True).stdout
    if staged:
        parser.error("Refusing staged changes; use a fresh clone for updated fixtures")
    with tempfile.TemporaryDirectory(prefix="verismo-svsm-index-") as temporary:
        env = {**os.environ, "GIT_INDEX_FILE": str(Path(temporary) / "index")}
        run("git", "read-tree", "HEAD", cwd=checkout, env=env)
        run("git", "apply", "--cached", "--recount", "-", cwd=checkout,
            env=env, input=patch, text=True)
        for source, target in FILES.items():
            blob = run("git", "hash-object", "-w", "--stdin", cwd=checkout,
                       input=(FIXTURES / source).read_bytes(), capture_output=True).stdout.strip()
            run("git", "update-index", "--add", "--cacheinfo",
                "100644", blob.decode("ascii"), target, cwd=checkout, env=env)
        changed = run("git", "diff", "--name-only", "--no-ext-diff", "--no-textconv",
                      "--ignore-submodules=none", "--", cwd=checkout,
                      env=env, capture_output=True, text=True).stdout
        extra = run("git", "ls-files", "--others", "--exclude-standard", cwd=checkout,
                    env=env, capture_output=True, text=True).stdout
        if changed or extra:
            parser.error(
                "Refusing unexpected checkout changes; no adapter files were overwritten:\n"
                + changed + extra
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    source = Path(os.environ["SVSM_SOURCE"]).resolve()
    checkout = Path(os.environ["SVSM_CHECKOUT"]).resolve()
    if checkout == source or checkout in source.parents or source in checkout.parents:
        parser.error("SVSM_CHECKOUT must be a separate disposable clone, not SVSM_SOURCE")
    if not checkout.exists():
        checkout.parent.mkdir(parents=True, exist_ok=True)
        run("git", "clone", "--shared", str(source), str(checkout), cwd=FIXTURES)
        run("git", "checkout", "--quiet", PIN, cwd=checkout)
    head = run("git", "rev-parse", "HEAD", cwd=checkout, capture_output=True, text=True).stdout.strip()
    if head != PIN:
        parser.error(f"SVSM_CHECKOUT must be at {PIN}, found {head}")
    packit = checkout / "packit"
    if not (packit / "Cargo.toml").exists():
        run("git", "clone", "--shared", str(source / "packit"), str(packit), cwd=checkout)
        run("git", "checkout", "--quiet", PACKIT_PIN, cwd=packit)
    packit_head = run("git", "rev-parse", "HEAD", cwd=packit,
                      capture_output=True, text=True).stdout.strip()
    if packit_head != PACKIT_PIN:
        parser.error(f"packit must be at {PACKIT_PIN}, found {packit_head}")
    packit_status = run("git", "status", "--porcelain", cwd=packit,
                        capture_output=True, text=True).stdout
    if packit_status:
        parser.error("Refusing a modified packit checkout")
    patch = (FIXTURES / "svsm.patch").read_text() + (FIXTURES / "svsm-lock.patch").read_text()
    patch = patch.replace("__VERISMO_PAGING__", PAGING.as_posix())
    applied = run("git", "diff", "--", "kernel/Cargo.toml", cwd=checkout,
                  capture_output=True, text=True).stdout
    if "verismo_paging" not in applied:
        status = run("git", "status", "--porcelain", cwd=checkout,
                     capture_output=True, text=True).stdout
        if status:
            parser.error("Refusing to patch a dirty checkout")
        run("git", "apply", "--recount", "--check", "-", cwd=checkout, input=patch, text=True)
        run("git", "apply", "--recount", "-", cwd=checkout, input=patch, text=True)
        for source_file, target in FILES.items():
            shutil.copyfile(FIXTURES / source_file, checkout / target)
    else:
        run("git", "apply", "--recount", "--reverse", "--check", "-", cwd=checkout,
            input=patch, text=True)
        check_installed(checkout, patch, parser)
    if not args.prepare_only:
        env = os.environ.copy()
        if "CARGO_ENCODED_RUSTFLAGS" in env or "RUSTFLAGS" in env:
            parser.error("unset RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS; SVSM's target flags must be retained")
        env.pop("SVSM_VERISMO_SUPPRESS_GLOBAL", None)
        run("cargo", "test", "--locked", "-p", "svsm-paging", "--test", "pgtable",
            cwd=checkout, env=env)
        run("cargo", "test", "--locked", "-p", "svsm", "--lib", "mm::",
            "--no-default-features", cwd=checkout, env=env)
        suppressed = {**env, "SVSM_VERISMO_SUPPRESS_GLOBAL": "1"}
        run("cargo", "test", "--locked", "-p", "svsm", "--lib", "mm::verismo_paging::tests",
            "--no-default-features", cwd=checkout, env=suppressed)
        run("cargo", "check", "--locked", "-p", "svsm", "--lib", "--bins",
            "--no-default-features", "--target", "x86_64-unknown-none", cwd=checkout, env=env)
        run("cargo", "build", "--locked", "-p", "svsm", "--bin", "svsm",
            "--no-default-features", "--target", "x86_64-unknown-none", cwd=checkout, env=env)


if __name__ == "__main__":
    main()

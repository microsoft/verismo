#!/usr/bin/env python3
"""Install or validate the bridge in an existing isolated LiteBox checkout."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


BASELINE = "8671b2439a78c789610acf3c7411eaac5fc3b312"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-installed", action="store_true")
    args = parser.parse_args()
    artifacts = Path(__file__).resolve().parent
    checkout = Path(os.environ["LITEBOX_CHECKOUT"]).resolve()
    paging = Path(os.environ.get("VERISMO_PAGING", artifacts.parents[1])).resolve()

    def git(*arguments, **kwargs):
        return subprocess.run(
            ["git", "-C", str(checkout), *arguments],
            check=True,
            text=True,
            capture_output=True,
            **kwargs,
        ).stdout

    if git("rev-parse", "HEAD").strip() != BASELINE:
        raise SystemExit(f"expected LiteBox baseline {BASELINE}")
    if not (paging / "Cargo.toml").is_file():
        raise SystemExit("VERISMO_PAGING must name the paging crate directory")
    patch = (artifacts / "litebox.patch").read_text().replace(
        '"__VERISMO_PAGING__"', json.dumps(str(paging))
    )
    destination = checkout / "litebox_platform_linux_kernel/src/arch/x86/mm"
    files = {"backend.rs": "verismo.rs", "backend_tests.rs": "verismo_tests.rs"}
    if args.check_installed:
        git("apply", "--reverse", "--check", "-", input=patch)
        with tempfile.TemporaryDirectory(prefix="litebox-patch-", dir=checkout.parent) as directory:
            environment = os.environ.copy()
            environment["GIT_INDEX_FILE"] = str(Path(directory) / "index")
            git("read-tree", BASELINE, env=environment)
            git("apply", "--cached", "--check", "--whitespace=error", "-", input=patch, env=environment)
        for source, target in files.items():
            if (artifacts / source).read_bytes() != (destination / target).read_bytes():
                raise SystemExit(f"{target} differs from retained adapter")
        print("Installed bridge matches; portable patch applies to the clean baseline.")
        return

    if git("status", "--porcelain").strip():
        raise SystemExit("refusing to patch a non-clean checkout; use an isolated local clone")
    git("apply", "--check", "-", input=patch)
    git("apply", "-", input=patch)
    for source, target in files.items():
        shutil.copyfile(artifacts / source, destination / target)
    print("Installed verismo-paging feature in the isolated LiteBox checkout.")


if __name__ == "__main__":
    main()

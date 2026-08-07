#!/bin/bash
# SPDX-License-Identifier: MIT
#
# Copyright (c) Microsoft Corporation
#
# Bump the pinned Verus version.
#
# Verus is pinned in two places that must move together: the five crates.io
# pins in source/Cargo.toml, and VERUS_VERSION / DEFAULT_VERUS_REV /
# VERUS_RUST_VERSION in tools/install_verus. This script finds the newest
# version published both as all five crates on crates.io and as a non-rolling
# Verus release, then rewrites both locations.
#
# Usage:
#   ./bump_verus.sh                  Bump to the newest common version.
#   ./bump_verus.sh --check          Report the target; change nothing.
#   ./bump_verus.sh --to 2026-07-27  Bump to a specific release date.
#
# Exit codes:
#   0  Files were updated (or, with --check, an update is available).
#   3  Already at the newest common version; nothing changed.
#   1  Error.

set -euo pipefail

VERUS_REPO=verus-lang/verus

# All five must publish a version before that date is a valid target; some
# dates are published for vstd but not for verus_builtin or verus_syn.
VERUS_CRATES=(
    vstd
    verus_builtin
    verus_builtin_macros
    verus_state_machines_macros
    verus_syn
)

REPO_ROOT="${BUMP_VERUS_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"

die() {
    echo "Error: $*" >&2
    exit 1
}

# Replace the contents of a file while preserving its permissions. BSD sed on
# macOS has no portable in-place flag, and `mv` from mktemp would drop the
# executable bit on tools/install_verus.
write_file() {
    local file=$1 tmp=$2
    cat "$tmp" > "$file"
    rm -f "$tmp"
}

apply_versions() {
    :
}

main() {
    die "not implemented yet"
}

# When sourced with BUMP_VERUS_LIB_ONLY=1, define functions but do not run.
if [ "${BUMP_VERUS_LIB_ONLY:-0}" = "1" ]; then
    return 0
fi

main "$@"

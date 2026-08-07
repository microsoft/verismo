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

# apply_versions ROOT CRATES_VERSION VERUS_VERSION VERUS_REV RUST_VERSION
#
# Rewrites the five crates.io pins in source/Cargo.toml and the three pinned
# variables in tools/install_verus. Asserts afterwards that every expected
# substitution landed, so a changed file format fails loudly instead of
# silently producing a half-updated tree.
apply_versions() {
    local root=$1 crates_version=$2 verus_version=$3 verus_rev=$4 rust_version=$5
    local cargo="$root/source/Cargo.toml"
    local install="$root/tools/install_verus"
    local tmp

    [ -f "$cargo" ] || die "not found: $cargo"
    [ -f "$install" ] || die "not found: $install"

    tmp=$(mktemp)
    sed -E "s/(version = \")=0\.0\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4}(\")/\1=${crates_version}\2/" \
        "$cargo" > "$tmp"
    write_file "$cargo" "$tmp"

    tmp=$(mktemp)
    sed -E \
        -e "s|^VERUS_VERSION=.*|VERUS_VERSION=${verus_version}|" \
        -e "s|^DEFAULT_VERUS_REV=.*|DEFAULT_VERUS_REV=${verus_rev}|" \
        -e "s|^VERUS_RUST_VERSION=.*|VERUS_RUST_VERSION=${rust_version}|" \
        "$install" > "$tmp"
    write_file "$install" "$tmp"

    local n
    n=$(grep -c "\"=${crates_version}\"" "$cargo" || true)
    [ "$n" -eq "${#VERUS_CRATES[@]}" ] \
        || die "expected ${#VERUS_CRATES[@]} pins in $cargo, updated $n"

    grep -q "^VERUS_VERSION=${verus_version}$" "$install" \
        || die "failed to update VERUS_VERSION in $install"
    grep -q "^DEFAULT_VERUS_REV=${verus_rev}$" "$install" \
        || die "failed to update DEFAULT_VERUS_REV in $install"
    grep -q "^VERUS_RUST_VERSION=${rust_version}$" "$install" \
        || die "failed to update VERUS_RUST_VERSION in $install"
}

main() {
    die "not implemented yet"
}

# When sourced with BUMP_VERUS_LIB_ONLY=1, define functions but do not run.
if [ "${BUMP_VERUS_LIB_ONLY:-0}" = "1" ]; then
    return 0
fi

main "$@"

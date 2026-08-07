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

require_commands() {
    local cmd
    for cmd in "$@"; do
        command -v "$cmd" > /dev/null 2>&1 || die "required command not found: $cmd"
    done
}

# Non-yanked 0.0.0-dated versions of one crate, e.g. 0.0.0-2026-08-02-0125.
crates_io_versions() {
    local crate=$1
    curl -sS --fail \
        -H 'User-Agent: verismo-verus-bump (https://github.com/microsoft/verismo)' \
        "https://crates.io/api/v1/crates/$crate/versions" \
        | jq -r '.versions[] | select(.yanked | not) | .num | select(startswith("0.0.0-2"))' \
        | sort -u
}

# Versions published for every crate in VERUS_CRATES, newest first.
common_crates_io_versions() {
    local acc="" crate versions
    for crate in "${VERUS_CRATES[@]}"; do
        versions=$(crates_io_versions "$crate")
        [ -n "$versions" ] || die "no dated versions found on crates.io for $crate"
        if [ -z "$acc" ]; then
            acc=$versions
        else
            acc=$(comm -12 <(printf '%s\n' "$acc") <(printf '%s\n' "$versions"))
        fi
    done
    printf '%s\n' "$acc" | sort -r
}

# Non-rolling Verus release versions, e.g. 0.2026.08.02.b677dd5.
verus_release_versions() {
    gh api "repos/$VERUS_REPO/releases" --paginate \
        -q '.[] | select(.prerelease | not) | .tag_name' \
        | sed -n 's|^release/||p' \
        | grep -v '/'
}

# 0.0.0-2026-08-02-0125 -> 2026-08-02
crates_version_date() {
    printf '%s\n' "${1#0.0.0-}" | cut -d- -f1-3
}

# 0.2026.08.02.b677dd5 -> 2026-08-02
release_version_date() {
    printf '%s\n' "$1" | cut -d. -f2-4 | tr '.' '-'
}

# Print "DATE CRATES_VERSION VERUS_VERSION" for the newest date published both
# as all five crates and as a non-rolling release. With an argument, use that
# date instead of the newest.
discover_target() {
    local wanted_date=${1:-}
    local releases crates_version release_version date

    releases=$(verus_release_versions)
    [ -n "$releases" ] || die "no Verus releases found"

    while read -r crates_version; do
        [ -n "$crates_version" ] || continue
        date=$(crates_version_date "$crates_version")
        if [ -n "$wanted_date" ] && [ "$date" != "$wanted_date" ]; then
            continue
        fi
        while read -r release_version; do
            [ -n "$release_version" ] || continue
            if [ "$(release_version_date "$release_version")" = "$date" ]; then
                printf '%s %s %s\n' "$date" "$crates_version" "$release_version"
                return 0
            fi
        done <<< "$releases"
    done <<< "$(common_crates_io_versions)"

    if [ -n "$wanted_date" ]; then
        die "no Verus release and crates.io publish found for date $wanted_date"
    fi
    die "no date is published both on crates.io and as a Verus release"
}

# Full 40-character commit SHA for a release's short SHA.
resolve_verus_rev() {
    gh api "repos/$VERUS_REPO/commits/$1" -q '.sha'
}

# The Rust toolchain that revision of Verus requires.
resolve_rust_version() {
    gh api "repos/$VERUS_REPO/contents/rust-toolchain.toml?ref=$1" \
        -H 'Accept: application/vnd.github.raw' \
        | sed -n 's/^channel *= *"\(.*\)"/\1/p'
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

usage() {
    cat <<EOF
Usage: $0 [OPTIONS]

Bump the pinned Verus version in source/Cargo.toml and tools/install_verus.

Options:
  --check           Report the target version without changing any files.
  --to YYYY-MM-DD   Bump to a specific release date instead of the newest.
  -h, --help        Show this help text.

Exit codes:
  0  Files were updated, or --check found an available update.
  3  Already at the target version; nothing changed.
  1  Error.
EOF
}

current_crates_version() {
    sed -nE 's/^vstd = \{ version = "=(0\.0\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4})".*/\1/p' \
        "$REPO_ROOT/source/Cargo.toml"
}

main() {
    local check_only=false wanted_date=""

    while [ "$#" -gt 0 ]; do
        case "$1" in
            --check) check_only=true ;;
            --to)
                [ "$#" -gt 1 ] || die "--to requires a date in YYYY-MM-DD form"
                wanted_date=$2
                shift
                ;;
            -h|--help) usage; exit 0 ;;
            *) usage >&2; die "unknown argument: $1" ;;
        esac
        shift
    done

    require_commands curl jq gh sed grep comm

    local target date crates_version verus_version
    target=$(discover_target "$wanted_date")
    read -r date crates_version verus_version <<< "$target"

    local current
    current=$(current_crates_version)
    [ -n "$current" ] || die "could not read the current pin from $REPO_ROOT/source/Cargo.toml"

    echo "current: $current"
    echo "target:  $crates_version ($verus_version, released $date)"

    if [ "$current" = "$crates_version" ]; then
        echo "Already at the target version; nothing to do."
        exit 3
    fi

    if $check_only; then
        echo "An update is available. Re-run without --check to apply it."
        exit 0
    fi

    local short_rev verus_rev rust_version
    short_rev=${verus_version##*.}
    verus_rev=$(resolve_verus_rev "$short_rev")
    [ -n "$verus_rev" ] || die "could not resolve the full SHA for $short_rev"
    rust_version=$(resolve_rust_version "$verus_rev")
    [ -n "$rust_version" ] || die "could not read the Rust channel for $verus_rev"

    apply_versions "$REPO_ROOT" "$crates_version" "$verus_version" "$verus_rev" "$rust_version"

    echo "Updated to $verus_version (rev $verus_rev, Rust $rust_version)."
    exit 0
}

# When sourced with BUMP_VERUS_LIB_ONLY=1, define functions but do not run.
if [ "${BUMP_VERUS_LIB_ONLY:-0}" = "1" ]; then
    return 0
fi

main "$@"

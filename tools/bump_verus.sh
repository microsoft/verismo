#!/bin/bash
# SPDX-License-Identifier: MIT
#
# Copyright (c) Microsoft Corporation
#
# Bump the pinned Verus version.
#
# Verus is pinned in two places: the five crates.io pins in source/Cargo.toml,
# and VERUS_VERSION / DEFAULT_VERUS_REV / VERUS_RUST_VERSION in
# tools/install_verus. This script selects the newest eligible publication for
# each crate independently and the newest stable, non-rolling Verus release.
#
# Usage:
#   ./bump_verus.sh                  Bump to the newest versions.
#   ./bump_verus.sh --check          Report the targets; change nothing.
#   ./bump_verus.sh --to 2026-07-27  Select versions no later than this date.
#
# Exit codes:
#   0  Files were updated (or, with --check, an update is available).
#   3  Already at the selected versions; nothing changed.
#   1  Error.

set -euo pipefail

VERUS_REPO=verus-lang/verus

# Each crate selects its newest eligible dated publication independently.
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
        | sort -ru
}

# Non-rolling Verus release versions, e.g. 0.2026.08.02.b677dd5.
verus_release_versions() {
    gh api "repos/$VERUS_REPO/releases" --paginate \
        -q '.[] | select(.prerelease | not) | .tag_name' \
        | sed -n 's|^release/||p' \
        | { grep -v '/' || [ $? -eq 1 ]; }
}

# 0.0.0-2026-08-02-0125 -> 2026-08-02
crates_version_date() {
    printf '%s\n' "${1#0.0.0-}" | cut -d- -f1-3
}

# 0.2026.08.02.b677dd5 -> 2026-08-02
release_version_date() {
    printf '%s\n' "$1" | cut -d. -f2-4 | tr '.' '-'
}

# Return success when DATE is no later than CUTOFF. An empty cutoff accepts all
# dates.
date_is_at_or_before() {
    local date=$1 cutoff=${2:-}
    [ -z "$cutoff" ] || [ "$date" = "$cutoff" ] || [[ "$date" < "$cutoff" ]]
}

# Newest non-yanked dated publication for one crate, optionally at or before
# an inclusive cutoff.
latest_crate_version() {
    local crate=$1 cutoff=${2:-}
    local version date versions

    versions=$(crates_io_versions "$crate" | sort -ru)
    [ -n "$versions" ] || die "no non-yanked dated version found for $crate"

    while read -r version; do
        [ -n "$version" ] || continue
        date=$(crates_version_date "$version")
        if date_is_at_or_before "$date" "$cutoff"; then
            printf '%s\n' "$version"
            return 0
        fi
    done <<< "$versions"

    if [ -n "$cutoff" ]; then
        die "no non-yanked $crate version found on or before $cutoff"
    fi
    die "no non-yanked dated version found for $crate"
}

# Newest stable, non-rolling Verus release, optionally at or before an
# inclusive cutoff.
latest_verus_release() {
    local cutoff=${1:-}
    local version date versions

    versions=$(verus_release_versions | sort -ru)
    [ -n "$versions" ] || die "no stable Verus releases found"

    while read -r version; do
        [ -n "$version" ] || continue
        date=$(release_version_date "$version")
        if date_is_at_or_before "$date" "$cutoff"; then
            printf '%s\n' "$version"
            return 0
        fi
    done <<< "$versions"

    if [ -n "$cutoff" ]; then
        die "no stable Verus release found at or before $cutoff"
    fi
    die "no stable Verus releases found"
}

# Print independently selected name=version targets in stable order.
discover_targets() {
    local cutoff=${1:-}
    local crate version

    for crate in "${VERUS_CRATES[@]}"; do
        version=$(latest_crate_version "$crate" "$cutoff")
        printf '%s=%s\n' "$crate" "$version"
    done
    version=$(latest_verus_release "$cutoff")
    printf 'VERUS_VERSION=%s\n' "$version"
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

# apply_versions ROOT VERUS_VERSION VERUS_REV RUST_VERSION CRATE=VERSION...
#
# Rewrites the five crates.io pins in source/Cargo.toml and the three pinned
# variables in tools/install_verus. Asserts afterwards that every expected
# substitution landed, so a changed file format fails loudly instead of
# silently producing a half-updated tree.
apply_versions() {
    local root=$1 verus_version=$2 verus_rev=$3 rust_version=$4
    local cargo="$root/source/Cargo.toml"
    local install="$root/tools/install_verus"
    local assignment crate version count tmp next_tmp install_tmp actual n
    local known variable expected

    shift 4
    [ "$#" -eq "${#VERUS_CRATES[@]}" ] \
        || die "expected ${#VERUS_CRATES[@]} crate assignments, got $#"

    for assignment in "$@"; do
        case "$assignment" in
            *=*) ;;
            *) die "invalid crate assignment: $assignment (expected CRATE=VERSION)" ;;
        esac
        crate=${assignment%%=*}
        version=${assignment#*=}
        known=0
        for expected in "${VERUS_CRATES[@]}"; do
            [ "$crate" = "$expected" ] && known=1
        done
        [ "$known" -eq 1 ] || die "unknown crate assignment: $crate"
        case "$version" in
            0.0.0-[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]-[0-9][0-9][0-9][0-9]) ;;
            *) die "invalid version for $crate: $version (expected 0.0.0-YYYY-MM-DD-NNNN)" ;;
        esac
    done

    [ -f "$cargo" ] || die "not found: $cargo"
    [ -f "$install" ] || die "not found: $install"

    for crate in "${VERUS_CRATES[@]}"; do
        count=0
        for assignment in "$@"; do
            [ "${assignment%%=*}" = "$crate" ] && count=$((count + 1))
        done
        [ "$count" -eq 1 ] \
            || die "expected exactly one $crate assignment, got $count"
    done

    tmp=$(mktemp)
    cat "$cargo" > "$tmp"
    for assignment in "$@"; do
        crate=${assignment%%=*}
        version=${assignment#*=}
        next_tmp=$(mktemp)
        sed -E \
            "s|^(${crate}[[:space:]]*=[[:space:]]*\\{[[:space:]]*version[[:space:]]*=[[:space:]]*\")=0\\.0\\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4}(\")|\\1=${version}\\2|" \
            "$tmp" > "$next_tmp"
        rm -f "$tmp"
        tmp=$next_tmp
    done

    install_tmp=$(mktemp)
    sed -E \
        -e "s|^VERUS_VERSION=.*|VERUS_VERSION=${verus_version}|" \
        -e "s|^DEFAULT_VERUS_REV=.*|DEFAULT_VERUS_REV=${verus_rev}|" \
        -e "s|^VERUS_RUST_VERSION=.*|VERUS_RUST_VERSION=${rust_version}|" \
        "$install" > "$install_tmp"

    for assignment in "$@"; do
        crate=${assignment%%=*}
        version=${assignment#*=}
        n=$(grep -Ec "^${crate}[[:space:]]*=" "$tmp" || true)
        [ "$n" -eq 1 ] \
            || die "expected exactly one $crate pin in $cargo, found $n"
        actual=$(sed -nE \
            "s|^${crate}[[:space:]]*=[[:space:]]*\\{[[:space:]]*version[[:space:]]*=[[:space:]]*\"=([^\"]+)\".*|\\1|p" \
            "$tmp")
        [ "$actual" = "$version" ] \
            || die "failed to update $crate in $cargo"
    done

    for variable in VERUS_VERSION DEFAULT_VERUS_REV VERUS_RUST_VERSION; do
        case "$variable" in
            VERUS_VERSION) expected=$verus_version ;;
            DEFAULT_VERUS_REV) expected=$verus_rev ;;
            VERUS_RUST_VERSION) expected=$rust_version ;;
        esac
        n=$(grep -Fxc "${variable}=${expected}" "$install_tmp" || true)
        [ "$n" -eq 1 ] \
            || die "expected exactly one $variable assignment in $install, found $n"
    done

    write_file "$cargo" "$tmp"
    write_file "$install" "$install_tmp"
}

usage() {
    cat <<EOF
Usage: $0 [OPTIONS]

Bump the pinned Verus version in source/Cargo.toml and tools/install_verus.

Options:
  --check           Report the target versions without changing any files.
  --to YYYY-MM-DD   Select the newest versions on or before YYYY-MM-DD.
  -h, --help        Show this help text.

Exit codes:
  0  Files were updated, or --check found an available update.
  3  Already at the target version; nothing changed.
  1  Error.
EOF
}

current_crate_version() {
    local crate=$1
    sed -nE \
        "s|^${crate}[[:space:]]*=[[:space:]]*\\{[[:space:]]*version[[:space:]]*=[[:space:]]*\"=(0\\.0\\.0-[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4})\".*|\\1|p" \
        "$REPO_ROOT/source/Cargo.toml"
}

current_verus_version() {
    sed -nE 's/^VERUS_VERSION=(.*)$/\1/p' "$REPO_ROOT/tools/install_verus"
}

targets_are_current() {
    local verus_version=$1 assignment crate target current
    local all_current=0
    shift

    [ "$#" -eq "${#VERUS_CRATES[@]}" ] \
        || die "expected ${#VERUS_CRATES[@]} crate assignments, got $#"

    for assignment in "$@"; do
        crate=${assignment%%=*}
        target=${assignment#*=}
        current=$(current_crate_version "$crate")
        [ -n "$current" ] \
            || die "could not read the current $crate pin from $REPO_ROOT/source/Cargo.toml"
        [ "$current" = "$target" ] || all_current=1
    done

    current=$(current_verus_version)
    [ -n "$current" ] \
        || die "could not read the current Verus release from $REPO_ROOT/tools/install_verus"
    [ "$current" = "$verus_version" ] || all_current=1

    return "$all_current"
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

    if [ -n "$wanted_date" ]; then
        case "$wanted_date" in
            [0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]) ;;
            *) die "--to requires a date in YYYY-MM-DD form" ;;
        esac
    fi

    require_commands curl jq gh sed grep

    local targets line expected crate version verus_version=""
    local index=0 current all_current=false
    local crate_assignments=()
    targets=$(discover_targets "$wanted_date")

    while IFS= read -r line; do
        if [ "$index" -lt "${#VERUS_CRATES[@]}" ]; then
            expected=${VERUS_CRATES[$index]}
            case "$line" in
                "$expected="*)
                    version=${line#*=}
                    [ -n "$version" ] || die "empty target version for $expected"
                    crate_assignments[${#crate_assignments[@]}]=$line
                    ;;
                *) die "expected target $expected at line $((index + 1)), got: $line" ;;
            esac
        elif [ "$index" -eq "${#VERUS_CRATES[@]}" ]; then
            case "$line" in
                VERUS_VERSION=*)
                    verus_version=${line#*=}
                    [ -n "$verus_version" ] || die "empty Verus release target"
                    ;;
                *) die "expected Verus release target at line $((index + 1)), got: $line" ;;
            esac
        else
            die "discover_targets returned more than six targets"
        fi
        index=$((index + 1))
    done <<< "$targets"

    [ "${#crate_assignments[@]}" -eq "${#VERUS_CRATES[@]}" ] \
        || die "expected ${#VERUS_CRATES[@]} crate targets, got ${#crate_assignments[@]}"
    [ "$index" -eq $((${#VERUS_CRATES[@]} + 1)) ] \
        || die "expected six targets, got $index"
    [ -n "$verus_version" ] || die "empty Verus release target"

    if targets_are_current "$verus_version" "${crate_assignments[@]}"; then
        all_current=true
    fi

    for line in "${crate_assignments[@]}"; do
        crate=${line%%=*}
        version=${line#*=}
        current=$(current_crate_version "$crate")
        echo "$crate: $current -> $version"
    done
    current=$(current_verus_version)
    echo "Verus release: $current -> $verus_version"

    if $all_current; then
        echo "Already at all selected target versions; nothing to do."
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

    apply_versions "$REPO_ROOT" "$verus_version" "$verus_rev" "$rust_version" \
        "${crate_assignments[@]}"

    echo "Updated to $verus_version (rev $verus_rev, Rust $rust_version)."
    exit 0
}

# When sourced with BUMP_VERUS_LIB_ONLY=1, define functions but do not run.
if [ "${BUMP_VERUS_LIB_ONLY:-0}" = "1" ]; then
    return 0
fi

main "$@"

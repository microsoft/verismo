#!/bin/bash
# SPDX-License-Identifier: MIT
#
# Copyright (c) Microsoft Corporation
#
# Offline unit tests for bump_verus.sh. These never touch the network: they
# source the script in library mode and exercise the file-rewriting logic
# against fixtures in a temp directory.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

FAILURES=0

fail() {
    echo "FAIL: $*" >&2
    FAILURES=$((FAILURES + 1))
}

pass() {
    echo "ok: $*"
}

check_eq() {
    local expected=$1 actual=$2 what=$3
    if [ "$expected" = "$actual" ]; then
        pass "$what"
    else
        fail "$what: expected '$expected', got '$actual'"
    fi
}

# Source the script without running main. It sets `set -e`, which would abort
# this harness on the first non-zero command, so turn that back off: these
# tests report failures rather than exiting on them.
BUMP_VERUS_LIB_ONLY=1 . "$SCRIPT_DIR/bump_verus.sh"
set +e

test_library_mode_defines_functions() {
    if declare -F apply_versions > /dev/null; then
        pass "library mode defines apply_versions"
    else
        fail "library mode did not define apply_versions"
    fi
}

test_library_mode_defines_functions


# Build a throwaway repo containing just the two files bump_verus.sh edits.
make_fixture_repo() {
    local root
    root=$(mktemp -d)
    mkdir -p "$root/source" "$root/tools"

    cat > "$root/source/Cargo.toml" <<'EOF'
[workspace.dependencies]
bitflags = "2.13"
paste = "1.0"

verus_builtin = { version = "=0.0.0-2026-08-02-0125", default-features = false }
verus_builtin_macros = { version = "=0.0.0-2026-08-02-0125", features = ["vpanic"], default-features = false }
verus_state_machines_macros = { version = "=0.0.0-2026-08-02-0125", default-features = false }
vstd = { version = "=0.0.0-2026-08-02-0125", features = ["alloc", "allow_panic"], default-features = false }

verus_syn = { version = "=0.0.0-2026-08-02-0125", features = ["full", "visit-mut", "extra-traits"] }
EOF

    cat > "$root/tools/install_verus" <<'EOF'
#!/bin/bash
# Verus release version and commit hash
VERUS_VERSION=0.2026.08.02.b677dd5
VERUS_RELEASE_TAG=release/$VERUS_VERSION
DEFAULT_VERUS_REV=b677dd5a766f25f56e9aa1e32621aa4e53304b47
VERUS_RUST_VERSION=1.97.1

# Verusfmt version
VERUSFMT_VERSION=v0.7.1
EOF
    chmod +x "$root/tools/install_verus"

    echo "$root"
}

test_apply_versions_rewrites_all_five_cargo_pins() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" "0.0.0-2026-07-27-0206" \
        "0.2026.07.27.31579f0" \
        "31579f0b8542a8a9ae4ae5604c16107ccde23ef2" \
        "1.97.1"

    local n
    n=$(grep -c '"=0.0.0-2026-07-27-0206"' "$root/source/Cargo.toml")
    check_eq "5" "$n" "all five Cargo.toml pins rewritten"

    n=$(grep -c '0.0.0-2026-08-02-0125' "$root/source/Cargo.toml" || true)
    check_eq "0" "$n" "no stale Cargo.toml pins remain"

    rm -rf "$root"
}

test_apply_versions_rewrites_install_verus() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" "0.0.0-2026-07-27-0206" \
        "0.2026.07.27.31579f0" \
        "31579f0b8542a8a9ae4ae5604c16107ccde23ef2" \
        "1.97.1"

    local install="$root/tools/install_verus"
    check_eq "VERUS_VERSION=0.2026.07.27.31579f0" \
        "$(grep '^VERUS_VERSION=' "$install")" "VERUS_VERSION rewritten"
    check_eq "DEFAULT_VERUS_REV=31579f0b8542a8a9ae4ae5604c16107ccde23ef2" \
        "$(grep '^DEFAULT_VERUS_REV=' "$install")" "DEFAULT_VERUS_REV rewritten"
    check_eq "VERUS_RUST_VERSION=1.97.1" \
        "$(grep '^VERUS_RUST_VERSION=' "$install")" "VERUS_RUST_VERSION rewritten"

    rm -rf "$root"
}

test_apply_versions_leaves_unrelated_lines_alone() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" "0.0.0-2026-07-27-0206" \
        "0.2026.07.27.31579f0" \
        "31579f0b8542a8a9ae4ae5604c16107ccde23ef2" \
        "1.97.1"

    check_eq 'bitflags = "2.13"' \
        "$(grep '^bitflags' "$root/source/Cargo.toml")" "unrelated dep untouched"
    check_eq "VERUSFMT_VERSION=v0.7.1" \
        "$(grep '^VERUSFMT_VERSION=' "$root/tools/install_verus")" "verusfmt pin untouched"
    check_eq 'VERUS_RELEASE_TAG=release/$VERUS_VERSION' \
        "$(grep '^VERUS_RELEASE_TAG=' "$root/tools/install_verus")" "release tag expression untouched"

    rm -rf "$root"
}

test_apply_versions_preserves_executable_bit() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" "0.0.0-2026-07-27-0206" \
        "0.2026.07.27.31579f0" \
        "31579f0b8542a8a9ae4ae5604c16107ccde23ef2" \
        "1.97.1"

    if [ -x "$root/tools/install_verus" ]; then
        pass "install_verus is still executable"
    else
        fail "install_verus lost its executable bit"
    fi

    rm -rf "$root"
}

test_apply_versions_rewrites_all_five_cargo_pins
test_apply_versions_rewrites_install_verus
test_apply_versions_leaves_unrelated_lines_alone
test_apply_versions_preserves_executable_bit

if [ "$FAILURES" -ne 0 ]; then
    echo "$FAILURES test(s) failed" >&2
    exit 1
fi
echo "All tests passed."

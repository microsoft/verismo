#!/bin/bash
# SPDX-License-Identifier: MIT
#
# Copyright (c) Microsoft Corporation
#
# Offline tests for bump_verus.sh. These never touch the network: they
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

test_workflow_provides_safe_outputs_to_bump_step() {
    local workflow="$SCRIPT_DIR/../.github/workflows/verus-bump.md"
    local bump_step
    bump_step=$(sed -n '/- name: Apply the version bump/,/- name: Install the new Verus toolchain/p' "$workflow")

    if grep -q 'GH_AW_SAFE_OUTPUTS:' <<< "$bump_step"; then
        pass "workflow provides GH_AW_SAFE_OUTPUTS to bump step"
    else
        fail "workflow does not provide GH_AW_SAFE_OUTPUTS to bump step"
    fi

    if grep -q 'mkdir -p.*GH_AW_SAFE_OUTPUTS' <<< "$bump_step"; then
        pass "workflow creates the safe outputs directory"
    else
        fail "workflow does not create the safe outputs directory"
    fi
}

test_workflow_provides_safe_outputs_to_bump_step

test_latest_verus_release_reports_no_eligible_releases() {
    local output status
    output=$(
        (
            gh() {
                printf '%s\n' "release/rolling/nightly"
            }
            set -euo pipefail
            latest_verus_release
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "no eligible Verus releases fails"
    check_eq "Error: no stable Verus releases found" "$output" \
        "no eligible Verus releases reports the explicit error"
}

test_latest_verus_release_reports_no_eligible_releases

test_latest_crate_version_reports_empty_source() {
    local output status
    output=$(
        (
            crates_io_versions() {
                :
            }
            set -euo pipefail
            latest_crate_version vstd
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "empty crate source fails"
    check_eq "Error: no non-yanked dated version found for vstd" "$output" \
        "empty crate source reports the explicit error"
}

test_latest_crate_version_reports_cutoff_without_eligible_version() {
    local output status
    output=$(
        (
            crates_io_versions() {
                printf '%s\n' \
                    "0.0.0-2026-08-09-0044" \
                    "0.0.0-2026-08-14-1234"
            }
            set -euo pipefail
            latest_crate_version vstd "2026-08-02"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "crate cutoff without eligible version fails"
    check_eq "Error: no non-yanked vstd version found on or before 2026-08-02" "$output" \
        "crate cutoff without eligible version reports the explicit error"
}

test_latest_crate_version_reports_empty_source
test_latest_crate_version_reports_cutoff_without_eligible_version

test_discover_targets_selects_each_source_independently() {
    local expected actual
    expected=$(cat <<'EOF'
vstd=0.0.0-2026-08-09-0044
verus_builtin=0.0.0-2026-08-09-0044
verus_builtin_macros=0.0.0-2026-08-09-0044
verus_state_machines_macros=0.0.0-2026-08-02-0125
verus_syn=0.0.0-2026-08-02-0125
VERUS_VERSION=0.2026.08.09.92f466f
EOF
)
    actual=$(
        crates_io_versions() {
            if [ "$1" = vstd ] || [ "$1" = verus_builtin ] \
                || [ "$1" = verus_builtin_macros ]; then
                printf '%s\n' \
                    "0.0.0-2026-08-02-0125" \
                    "0.0.0-2026-08-09-0044"
            else
                printf '%s\n' \
                    "0.0.0-2026-07-27-0206" \
                    "0.0.0-2026-08-02-0125"
            fi
        }
        verus_release_versions() {
            printf '%s\n' \
                "0.2026.08.02.b677dd5" \
                "0.2026.08.09.92f466f"
        }
        discover_targets
    )
    check_eq "$expected" "$actual" "each source selects its newest version independently"
}

test_discover_targets_honors_inclusive_cutoff() {
    local expected actual
    expected=$(cat <<'EOF'
vstd=0.0.0-2026-08-09-0044
verus_builtin=0.0.0-2026-08-09-0044
verus_builtin_macros=0.0.0-2026-08-09-0044
verus_state_machines_macros=0.0.0-2026-08-09-0044
verus_syn=0.0.0-2026-08-09-0044
VERUS_VERSION=0.2026.08.09.92f466f
EOF
)
    actual=$(
        crates_io_versions() {
            printf '%s\n' \
                "0.0.0-2026-08-02-0125" \
                "0.0.0-2026-08-09-0044" \
                "0.0.0-2026-08-14-1234"
        }
        verus_release_versions() {
            printf '%s\n' \
                "0.2026.08.02.b677dd5" \
                "0.2026.08.09.92f466f" \
                "0.2026.08.14.abcdef0"
        }
        discover_targets "2026-08-09"
    )
    check_eq "$expected" "$actual" "cutoff includes 08-09 and excludes 08-14 for every source"
}

test_discover_targets_selects_each_source_independently
test_discover_targets_honors_inclusive_cutoff


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

snapshot_fixture() {
    local root=$1
    cp "$root/source/Cargo.toml" "$root/Cargo.toml.before"
    cp "$root/tools/install_verus" "$root/install_verus.before"
}

check_fixture_unchanged() {
    local root=$1 what=$2
    if cmp -s "$root/Cargo.toml.before" "$root/source/Cargo.toml"; then
        pass "$what leaves Cargo fixture byte-for-byte unchanged"
    else
        fail "$what changed Cargo fixture"
    fi
    if cmp -s "$root/install_verus.before" "$root/tools/install_verus"; then
        pass "$what leaves install fixture byte-for-byte unchanged"
    else
        fail "$what changed install fixture"
    fi
}

test_main_check_reports_independent_targets() {
    local root; root=$(make_fixture_repo)
    local output status expected
    output=$(
        (
            BUMP_VERUS_REPO_ROOT=$root
            REPO_ROOT=$root
            discover_targets() {
                cat <<'EOF'
vstd=0.0.0-2026-08-09-0044
verus_builtin=0.0.0-2026-08-10-0055
verus_builtin_macros=0.0.0-2026-08-02-0125
verus_state_machines_macros=0.0.0-2026-08-12-0077
verus_syn=0.0.0-2026-08-13-0088
VERUS_VERSION=0.2026.08.09.92f466f
EOF
            }
            main --check
        ) 2>&1
    )
    status=$?
    expected=$(cat <<'EOF'
vstd: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-09-0044
verus_builtin: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-10-0055
verus_builtin_macros: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
verus_state_machines_macros: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-12-0077
verus_syn: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-13-0088
Verus release: 0.2026.08.02.b677dd5 -> 0.2026.08.09.92f466f
An update is available. Re-run without --check to apply it.
EOF
)

    check_eq "0" "$status" "main --check succeeds when any independent target differs"
    check_eq "$expected" "$output" "main --check reports every independent current and target"

    rm -rf "$root"
}

test_main_check_returns_three_only_when_all_targets_match() {
    local root; root=$(make_fixture_repo)
    local output status expected
    output=$(
        (
            BUMP_VERUS_REPO_ROOT=$root
            REPO_ROOT=$root
            discover_targets() {
                cat <<'EOF'
vstd=0.0.0-2026-08-02-0125
verus_builtin=0.0.0-2026-08-02-0125
verus_builtin_macros=0.0.0-2026-08-02-0125
verus_state_machines_macros=0.0.0-2026-08-02-0125
verus_syn=0.0.0-2026-08-02-0125
VERUS_VERSION=0.2026.08.02.b677dd5
EOF
            }
            main --check
        ) 2>&1
    )
    status=$?
    expected=$(cat <<'EOF'
vstd: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
verus_builtin: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
verus_builtin_macros: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
verus_state_machines_macros: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
verus_syn: 0.0.0-2026-08-02-0125 -> 0.0.0-2026-08-02-0125
Verus release: 0.2026.08.02.b677dd5 -> 0.2026.08.02.b677dd5
Already at all selected target versions; nothing to do.
EOF
)

    check_eq "3" "$status" "main --check returns three only when all six targets match"
    check_eq "$expected" "$output" "main --check reports all matching targets without a shared summary"

    rm -rf "$root"
}

test_apply_versions_rewrites_mixed_cargo_pins() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" \
        "0.2026.08.09.92f466f" \
        "92f466f1234567890abcdef1234567890abcdef1" \
        "1.98.0" \
        "vstd=0.0.0-2026-08-09-0044" \
        "verus_builtin=0.0.0-2026-08-10-0055" \
        "verus_builtin_macros=0.0.0-2026-08-11-0066" \
        "verus_state_machines_macros=0.0.0-2026-08-12-0077" \
        "verus_syn=0.0.0-2026-08-13-0088"

    local n
    check_eq \
        'vstd = { version = "=0.0.0-2026-08-09-0044", features = ["alloc", "allow_panic"], default-features = false }' \
        "$(grep '^vstd =' "$root/source/Cargo.toml")" "vstd pin and options rewritten"
    check_eq \
        'verus_builtin = { version = "=0.0.0-2026-08-10-0055", default-features = false }' \
        "$(grep '^verus_builtin =' "$root/source/Cargo.toml")" "verus_builtin pin and options rewritten"
    check_eq \
        'verus_builtin_macros = { version = "=0.0.0-2026-08-11-0066", features = ["vpanic"], default-features = false }' \
        "$(grep '^verus_builtin_macros =' "$root/source/Cargo.toml")" \
        "verus_builtin_macros pin and options rewritten"
    check_eq \
        'verus_state_machines_macros = { version = "=0.0.0-2026-08-12-0077", default-features = false }' \
        "$(grep '^verus_state_machines_macros =' "$root/source/Cargo.toml")" \
        "verus_state_machines_macros pin and options rewritten"
    check_eq \
        'verus_syn = { version = "=0.0.0-2026-08-13-0088", features = ["full", "visit-mut", "extra-traits"] }' \
        "$(grep '^verus_syn =' "$root/source/Cargo.toml")" \
        "verus_syn pin and options rewritten"

    n=$(grep -Ec '^(vstd|verus_builtin|verus_builtin_macros|verus_state_machines_macros|verus_syn) = .*0\.0\.0-2026-08-02-0125' \
        "$root/source/Cargo.toml" || true)
    check_eq "0" "$n" "stale fixture pins are absent from all updated crate lines"

    rm -rf "$root"
}

test_apply_versions_rewrites_install_verus() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" \
        "0.2026.08.09.92f466f" \
        "92f466f1234567890abcdef1234567890abcdef1" \
        "1.98.0" \
        "vstd=0.0.0-2026-08-09-0044" \
        "verus_builtin=0.0.0-2026-08-09-0044" \
        "verus_builtin_macros=0.0.0-2026-08-09-0044" \
        "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
        "verus_syn=0.0.0-2026-08-02-0125"

    local install="$root/tools/install_verus"
    check_eq "VERUS_VERSION=0.2026.08.09.92f466f" \
        "$(grep '^VERUS_VERSION=' "$install")" "VERUS_VERSION rewritten"
    check_eq "DEFAULT_VERUS_REV=92f466f1234567890abcdef1234567890abcdef1" \
        "$(grep '^DEFAULT_VERUS_REV=' "$install")" "DEFAULT_VERUS_REV rewritten"
    check_eq "VERUS_RUST_VERSION=1.98.0" \
        "$(grep '^VERUS_RUST_VERSION=' "$install")" "VERUS_RUST_VERSION rewritten"

    rm -rf "$root"
}

test_apply_versions_leaves_unrelated_lines_alone() {
    local root; root=$(make_fixture_repo)
    apply_versions "$root" \
        "0.2026.08.09.92f466f" \
        "92f466f1234567890abcdef1234567890abcdef1" \
        "1.98.0" \
        "vstd=0.0.0-2026-08-09-0044" \
        "verus_builtin=0.0.0-2026-08-09-0044" \
        "verus_builtin_macros=0.0.0-2026-08-09-0044" \
        "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
        "verus_syn=0.0.0-2026-08-02-0125"

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
    apply_versions "$root" \
        "0.2026.08.09.92f466f" \
        "92f466f1234567890abcdef1234567890abcdef1" \
        "1.98.0" \
        "vstd=0.0.0-2026-08-09-0044" \
        "verus_builtin=0.0.0-2026-08-09-0044" \
        "verus_builtin_macros=0.0.0-2026-08-09-0044" \
        "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
        "verus_syn=0.0.0-2026-08-02-0125"

    if [ -x "$root/tools/install_verus" ]; then
        pass "install_verus is still executable"
    else
        fail "install_verus lost its executable bit"
    fi

    rm -rf "$root"
}

test_apply_versions_requires_five_crate_assignments() {
    local root; root=$(make_fixture_repo)
    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09-0044" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "fewer than five crate assignments fails"
    check_eq "Error: expected 5 crate assignments, got 4" "$output" \
        "fewer than five crate assignments reports the explicit error"
    check_fixture_unchanged "$root" "missing crate assignment"

    rm -rf "$root"
}

test_apply_versions_rejects_duplicate_crate_assignment() {
    local root; root=$(make_fixture_repo)
    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09-0044" \
                "vstd=0.0.0-2026-08-02-0125" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "duplicate crate assignment fails"
    check_eq "Error: expected exactly one vstd assignment, got 2" "$output" \
        "duplicate crate assignment reports the explicit error"
    check_fixture_unchanged "$root" "duplicate crate assignment"

    rm -rf "$root"
}

test_apply_versions_rejects_unknown_crate_assignment() {
    local root; root=$(make_fixture_repo)
    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09-0044" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                "unknown=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "unknown crate assignment fails"
    check_eq "Error: unknown crate assignment: unknown" "$output" \
        "unknown crate assignment reports the explicit error"
    check_fixture_unchanged "$root" "unknown crate assignment"

    rm -rf "$root"
}

test_apply_versions_rejects_bare_crate_assignment_without_rewriting() {
    local root; root=$(make_fixture_repo)
    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                "verus_syn=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "bare crate assignment fails"
    check_eq "Error: invalid crate assignment: vstd (expected CRATE=VERSION)" "$output" \
        "bare crate assignment reports the explicit error"
    check_fixture_unchanged "$root" "bare crate assignment"

    rm -rf "$root"
}

test_apply_versions_rejects_invalid_crate_version_without_rewriting() {
    local root; root=$(make_fixture_repo)
    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                "verus_syn=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "invalid crate version fails"
    check_eq \
        "Error: invalid version for vstd: 0.0.0-2026-08-09 (expected 0.0.0-YYYY-MM-DD-NNNN)" \
        "$output" "invalid crate version reports the explicit error"
    check_fixture_unchanged "$root" "invalid crate version"

    rm -rf "$root"
}

test_apply_versions_rejects_invalid_toolchain_assignments_without_rewriting() {
    local variable condition root assignment found output status

    for variable in VERUS_VERSION DEFAULT_VERUS_REV VERUS_RUST_VERSION; do
        for condition in missing duplicate; do
            root=$(make_fixture_repo)
            if [ "$condition" = missing ]; then
                sed "/^${variable}=/d" "$root/tools/install_verus" \
                    > "$root/tools/install_verus.new"
                write_file "$root/tools/install_verus" "$root/tools/install_verus.new"
                found=0
            else
                assignment=$(grep "^${variable}=" "$root/tools/install_verus")
                printf '%s\n' "$assignment" >> "$root/tools/install_verus"
                found=2
            fi
            snapshot_fixture "$root"

            output=$(
                (
                    set -euo pipefail
                    apply_versions "$root" \
                        "0.2026.08.09.92f466f" \
                        "92f466f1234567890abcdef1234567890abcdef1" \
                        "1.98.0" \
                        "vstd=0.0.0-2026-08-09-0044" \
                        "verus_builtin=0.0.0-2026-08-09-0044" \
                        "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                        "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                        "verus_syn=0.0.0-2026-08-02-0125"
                ) 2>&1
            )
            status=$?

            check_eq "1" "$status" "$condition $variable assignment fails"
            check_eq \
                "Error: expected exactly one $variable assignment in $root/tools/install_verus, found $found" \
                "$output" "$condition $variable assignment reports the explicit error"
            check_fixture_unchanged "$root" "$condition $variable assignment"

            rm -rf "$root"
        done
    done
}

test_apply_versions_rejects_missing_cargo_target() {
    local root; root=$(make_fixture_repo)
    sed '/^verus_syn =/d' "$root/source/Cargo.toml" > "$root/source/Cargo.toml.new"
    write_file "$root/source/Cargo.toml" "$root/source/Cargo.toml.new"

    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09-0044" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                "verus_syn=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "missing Cargo target fails"
    check_eq "Error: expected exactly one verus_syn pin in $root/source/Cargo.toml, found 0" \
        "$output" "missing Cargo target reports the explicit error"
    check_fixture_unchanged "$root" "missing Cargo target"

    rm -rf "$root"
}

test_apply_versions_rejects_duplicate_cargo_target() {
    local root; root=$(make_fixture_repo)
    printf '%s\n' \
        'vstd = { version = "=0.0.0-2026-08-02-0125", default-features = false }' \
        >> "$root/source/Cargo.toml"

    local output status
    snapshot_fixture "$root"
    output=$(
        (
            set -euo pipefail
            apply_versions "$root" \
                "0.2026.08.09.92f466f" \
                "92f466f1234567890abcdef1234567890abcdef1" \
                "1.98.0" \
                "vstd=0.0.0-2026-08-09-0044" \
                "verus_builtin=0.0.0-2026-08-09-0044" \
                "verus_builtin_macros=0.0.0-2026-08-09-0044" \
                "verus_state_machines_macros=0.0.0-2026-08-02-0125" \
                "verus_syn=0.0.0-2026-08-02-0125"
        ) 2>&1
    )
    status=$?

    check_eq "1" "$status" "duplicate Cargo target fails"
    check_eq "Error: expected exactly one vstd pin in $root/source/Cargo.toml, found 2" \
        "$output" "duplicate Cargo target reports the explicit error"
    check_fixture_unchanged "$root" "duplicate Cargo target"

    rm -rf "$root"
}

test_apply_versions_rewrites_mixed_cargo_pins
test_apply_versions_rewrites_install_verus
test_apply_versions_leaves_unrelated_lines_alone
test_apply_versions_preserves_executable_bit
test_apply_versions_requires_five_crate_assignments
test_apply_versions_rejects_duplicate_crate_assignment
test_apply_versions_rejects_unknown_crate_assignment
test_apply_versions_rejects_bare_crate_assignment_without_rewriting
test_apply_versions_rejects_invalid_crate_version_without_rewriting
test_apply_versions_rejects_invalid_toolchain_assignments_without_rewriting
test_apply_versions_rejects_missing_cargo_target
test_apply_versions_rejects_duplicate_cargo_target
test_main_check_reports_independent_targets
test_main_check_returns_three_only_when_all_targets_match

if [ "$FAILURES" -ne 0 ]; then
    echo "$FAILURES test(s) failed" >&2
    exit 1
fi
echo "All tests passed."

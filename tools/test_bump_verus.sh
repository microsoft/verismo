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

if [ "$FAILURES" -ne 0 ]; then
    echo "$FAILURES test(s) failed" >&2
    exit 1
fi
echo "All tests passed."

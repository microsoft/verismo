#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

export GUEST_EXAMPLE=kvm-smp-guest
export GUEST_FEATURE=kvm-smp-test
export LINKER_SCRIPT="$SCRIPT_DIR/x86_64-pvh-smp.ld"
export SUCCESS_MARKER=VERIOS_PAGETABLE_SMP_BOOT_OK
export GUEST_SMP=4
export BOOT_TIMEOUT_SECONDS=${BOOT_TIMEOUT_SECONDS:-30}

exec "$SCRIPT_DIR/run.sh"

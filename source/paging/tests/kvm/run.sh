#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
PAGING_DIR=$(cd -- "$SCRIPT_DIR/../.." && pwd)
SOURCE_DIR=$(cd -- "$PAGING_DIR/.." && pwd)
TARGET_DIR=${CARGO_TARGET_DIR:-"$SOURCE_DIR/target"}
GUEST="$TARGET_DIR/x86_64-unknown-none/release/examples/kvm-guest"
SUCCESS_MARKER=VERIOS_PAGETABLE_BOOT_OK
BOOT_TIMEOUT_SECONDS=${BOOT_TIMEOUT_SECONDS:-15}
ACTIVE_PID=
ACTIVE_LOG=

export CARGO_ENCODED_RUSTFLAGS=$'--cfg\x1ftarget_min_page="4kib"\x1f-C\x1flink-arg=-T'"$SCRIPT_DIR"$'/x86_64-pvh.ld\x1f-C\x1frelocation-model=static'
export RUSTC_BOOTSTRAP=1

cleanup() {
    if [[ -n "$ACTIVE_PID" ]] && kill -0 "$ACTIVE_PID" 2>/dev/null; then
        kill "$ACTIVE_PID"
    fi
    if [[ -n "$ACTIVE_PID" ]]; then
        wait "$ACTIVE_PID" 2>/dev/null || true
    fi
    if [[ -n "$ACTIVE_LOG" ]]; then
        rm -f -- "$ACTIVE_LOG"
    fi
}
trap cleanup EXIT INT TERM

(
    cd "$SOURCE_DIR"
    cargo build \
        --quiet \
        -Z build-std=core,alloc \
        --target x86_64-unknown-none \
        --release \
        --no-default-features \
        --features kvm-test \
        -p verios-pagetable-beta \
        --example kvm-guest
)

run_vmm() {
    local name=$1
    shift
    ACTIVE_LOG=$(mktemp)
    "$@" >"$ACTIVE_LOG" 2>&1 &
    ACTIVE_PID=$!
    local ticks=$((BOOT_TIMEOUT_SECONDS * 10))

    for ((tick = 0; tick < ticks; tick++)); do
        if grep -q "$SUCCESS_MARKER" "$ACTIVE_LOG"; then
            cleanup
            ACTIVE_PID=
            ACTIVE_LOG=
            echo "$name: $SUCCESS_MARKER"
            return 0
        fi
        if ! kill -0 "$ACTIVE_PID" 2>/dev/null; then
            break
        fi
        sleep 0.1
    done

    echo "$name failed to produce $SUCCESS_MARKER" >&2
    sed -n '1,120p' "$ACTIVE_LOG" >&2
    cleanup
    ACTIVE_PID=
    ACTIVE_LOG=
    return 1
}

passed=0
attempted=0

if command -v qemu-system-x86_64 >/dev/null 2>&1; then
    attempted=$((attempted + 1))
    qemu_accel=(-machine q35,accel=tcg -cpu max)
    if [[ -r /dev/kvm && -w /dev/kvm ]]; then
        qemu_accel=(-machine q35,accel=kvm -cpu host)
    fi
    if run_vmm QEMU \
        qemu-system-x86_64 \
        "${qemu_accel[@]}" \
        -m 128M \
        -smp 1 \
        -display none \
        -monitor none \
        -serial stdio \
        -no-reboot \
        -kernel "$GUEST" \
        -device isa-debug-exit,iobase=0xf4,iosize=0x04; then
        passed=$((passed + 1))
    fi
fi

if command -v cloud-hypervisor >/dev/null 2>&1 && [[ -r /dev/kvm && -w /dev/kvm ]]; then
    attempted=$((attempted + 1))
    if run_vmm Cloud-Hypervisor \
        cloud-hypervisor \
        --kernel "$GUEST" \
        --cpus boot=1 \
        --memory size=128M \
        --serial tty \
        --console off; then
        passed=$((passed + 1))
    fi
fi

if ((attempted == 0)); then
    echo "No runnable VMM found: install qemu-system-x86_64, or install cloud-hypervisor with accessible /dev/kvm." >&2
    exit 1
fi
if ((passed != attempted)); then
    exit 1
fi

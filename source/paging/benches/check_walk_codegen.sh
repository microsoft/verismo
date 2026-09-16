#!/usr/bin/env bash
set -euo pipefail

source_root="$(cd "$(dirname "$0")/../.." && pwd)"
target="x86_64-unknown-linux-gnu"

cd "$source_root"
cargo bench -p paging --bench paging_compare --target "$target" --no-run --quiet

binary="$(
    find "target/$target/release/deps" -maxdepth 1 -type f \
        -name 'paging_compare-*' -perm -111 -printf '%T@ %p\n' |
        sort -nr |
        head -1 |
        cut -d' ' -f2-
)"
symbol="$(
    nm -S --size-sort -C "$binary" |
        grep -F '<paging_compare::current::CurrentAdapter as paging_compare::common::PagingAdapter>::translate' |
        head -1 || true
)"

if [[ -z "$symbol" ]]; then
    symbol="$(
        nm -S --size-sort -C "$binary" |
            grep -F 'paging_compare::execute_thread::<paging_compare::current::CurrentAdapter>' |
            head -1 || true
    )"
    expected_back_edges=19
else
    expected_back_edges=0
fi

read -r start size _ <<<"$symbol"
stop="$(printf '0x%x' "$((16#$start + 16#$size))")"
back_edges=0

while read -r from to; do
    if ((16#$to < 16#$from)); then
        ((back_edges += 1))
    fi
done < <(
    objdump -d --start-address="0x$start" --stop-address="$stop" "$binary" |
        sed -nE 's/^[[:space:]]*([0-9a-f]+):.*[[:space:]]j[a-z]+[[:space:]]+([0-9a-f]+).*/\1 \2/p'
)

# Translation is loop-free; the inlined benchmark body has nineteen back edges
# from its surrounding workloads and control flow.
if ((back_edges != expected_back_edges)); then
    echo "expected $expected_back_edges translation-body back edges, found $back_edges" >&2
    exit 1
fi

echo "walk codegen remains unrolled"

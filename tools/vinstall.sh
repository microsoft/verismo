#!/bin/bash
# Determine the directory that this script is in
if [ "$BASH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
elif [ "$ZSH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${(%):-%N}" )" >/dev/null 2>&1 && pwd )"
else
  echo "Unknown shell; exiting."
  return 1
fi
TOOLS_DIR=$(realpath $SCRIPT_DIR)
cargo install --path $TOOLS_DIR/cargo-v
cargo install --path $TOOLS_DIR/verus-rustc
cd source
builtin=`cargo metadata --format-version 1 | jq -r '.packages[] | select(.name == "builtin_macros") | .targets[].src_path'`
verus=`dirname $builtin`/../../../source/target-verus/release/verus
if [ -f ${verus} ]; then
echo "verus (${verus}) is already built"
else
cargo v prepare-verus 
fi
curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.4.3/verusfmt-installer.sh | sh

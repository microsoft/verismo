#!/bin/bash
SCRIPT=$(readlink -f $0)
SCRIPT_DIR=`dirname $SCRIPT`
TOP_DIR=$SCRIPT_DIR/..

if [ -z "$RUST_DIR" ]; then
RUST_DIR=$TOP_DIR/verus/rust
fi
if [ -z "$Z3_PATH" ]; then
Z3_PATH=/usr/bin/z3
fi
echo "Z3_PATH:" $Z3_PATH

if [ -z "$VERIFIER_PATH" ]; then
#/root/snp/verus-snp/verus/source/target/debug/rust_verify
VERIFIER_PATH=$TOP_DIR/verus/source/target-verus/release/verus
fi
echo "VERIFIER_PATH:" $VERIFIER_PATH

TARGET=$1
MODULE=$2
p=${MODULE//::/\/}
MODULES=`find monitor_mod/src/$p -name "*.rs" -type f -print `
echo "$MODULES" >> modules.log
MODULES=${MODULES//monitor_mod\/src\//}
MODULES=${MODULES//\/mod.rs/}
MODULES=${MODULES//\//::}
MODULES=${MODULES//.rs/}
echo "$MODULES" >> modules.log
VERUS_DIR=$TOP_DIR/verus
EXTRA=${@:3} \
MODULES=$MODULES \
VERUS_SNP_DIR=$TOP_DIR \
VERUS_DIR=$VERUS_DIR \
RUSTC=$SCRIPT_DIR/rust_verify.sh \
VERIFIER_PATH=$VERIFIER_PATH \
Z3_PATH=$Z3_PATH \
TARGET=$TARGET \
MODULE=$MODULE \
cargo build --package=$1  --release --target $TOP_DIR/source/target.json -Zbuild-std=core,alloc --verbose


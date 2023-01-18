#!/bin/bash
SCRIPT=$(readlink -f $0)
SCRIPT_DIR=`dirname $SCRIPT`
TOP_DIR=$SCRIPT_DIR/..
RUST_DIR=$TOP_DIR/verus/rust
if [ -z "$Z3_PATH" ]; then
Z3_PATH=$TOP_DIR/verus/source/z3
fi
echo "Z3_PATH:" $Z3_PATH

if [ -z "$VERIFIER_PATH" ]; then
#/root/snp/verus-snp/verus/source/target/debug/rust_verify
VERIFIER_PATH=$TOP_DIR/verus/source/target/debug/rust_verify
fi
echo "VERIFIER_PATH:" $VERIFIER_PATH
TARGET=$1
MODULE=$2

if [ "$MODULE" == "parallel" ]; then
MODULES=`$RUST_DIR/install/bin/cargo modules generate graph --package monitor_mod |grep "\"mod\" node" |cut -f 1 -d "["`
else
MODULES=""
fi
EXTRA=${@:3} \
MODULES=$MODULES \
VERUS_SNP_DIR=$TOP_DIR \
RUSTC=$SCRIPT_DIR/rust_verify.sh \
RUST_DIR=$RUST_DIR \
VERIFIER_PATH=$VERIFIER_PATH \
Z3_PATH=$Z3_PATH \
TARGET=$TARGET \
MODULE=$MODULE \
$RUST_DIR/install/bin/cargo fmt 

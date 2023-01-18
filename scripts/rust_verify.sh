#!/bin/bash
# The script will
#   * pick rustc as RUSTC if the crate is not the TARGET crate
#   * pick veus_verify as RUSTC if a crate is the TARGET crate
SCRIPT=$(readlink -f $0)
SCRIPT_DIR=`dirname $SCRIPT`
TOP_DIR=$SCRIPT_DIR/..
VERUS_SNP_DIR=$TOP_DIR
if [ -z "$Z3_PATH" ]; then
Z3_PATH=/usr/bin/z3
fi

if [ -z "$VERIFIER_PATH" ]; then
#/root/snp/verus-snp/verus/source/target/debug/rust_verify
VERIFIER_PATH=$TOP_DIR/verus/source/target-verus/debug/veru
fi
case $(uname -m) in
  x86_64)
    ARCH=x86_64
    ;;
  arm64)
    ARCH=aarch64
    ;;
  *)
    echo "Unknown architecture $(uname -m)" 1>&2
    exit 1
    ;;
esac


# # Update library path
# if [ "$(uname)" == "Darwin" ]; then
#     ARCH_NAME=${ARCH}-apple-darwin
#     export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:"$RUST_DIR/install/lib/rustlib/${ARCH_NAME}/lib"
# elif [ "$(uname)" == "Linux" ]; then
#     ARCH_NAME=${ARCH}-unknown-linux-gnu
#     export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:"$RUST_DIR/install/lib/rustlib/${ARCH_NAME}/lib"
# fi

# # Add rust-lld path
# export PATH=$PATH:"$RUST_DIR/build/${ARCH_NAME}/stage0/lib/rustlib/${ARCH_NAME}/bin/"
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${VERUS_DIR}/source/target/release/deps
function run_verus_verify()
{
    VERUS_Z3_PATH=$Z3_PATH \
    $VERIFIER_PATH \
    $@ --log-all --log-dir ./.rust_verify/ --rlimit=5000 --no-solver-version-check --no-builtin --arch-word-bits 64
}


echo "" > cmd.log
if [ -z "$MODULE" ]; then
    extra=""
elif [ "$MODULE" == "root" ]; then
    extra="--verify-root"
else
    echo "$MODULES" >> cmd.log
    extra="--verify-module $MODULE"
    for mod in $MODULES; do
        m=${mod/$TARGET::/};
        m=${m//\"/};
        echo "$m" >> cmd.log
        if [[ $m == $MODULE* ]];then
            extra="$extra --verify-module $m"
        fi
    done
    echo "$extra" >> cmd.log
    #extra="--verify-module $MODULE"
fi
if [[ "$@" == *"--crate-name $TARGET monitor_mod/src/lib.rs"* ]]; then
    echo "$VERIFIER_PATH" $@ $extra>> /tmp/cmd.log
    RUSTFLAGS=$RUSTFLAGS \
    run_verus_verify $@ $extra $EXTRA --compile 
elif [[ "$@" == *"--crate-name $TARGET "* ]]; then
    echo "$VERIFIER_PATH" $@ $extra>> /tmp/cmd.log
    RUSTFLAGS=$RUSTFLAGS \
    run_verus_verify  $@ --compile
elif [[ "$@" == *"--crate-name vstd"* ]]; then
    echo "$VERIFIER_PATH" $@ $extra >> /tmp/cmd.log
    RUSTFLAGS="$RUSTFLAGS --cfg proc_macro_span --cfg verus_keep_ghost" \
    run_verus_verify $@ --compile --no-verify --no-vstd --cfg proc_macro_span --cfg verus_keep_ghost
else
    echo "rustc " $@ >> /tmp/cmd.log
    RUSTFLAGS="$RUSTFLAGS --cfg proc_macro_span --cfg verus_keep_ghost" \
    rustc $@ --cfg proc_macro_span --cfg verus_keep_ghost
    #$RUST_DIR/install/bin/rustc $@
fi


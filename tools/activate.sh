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

echo "building verus-rustc."
(
    cargo install --path $TOOLS_DIR/verus-rustc
    cargo install --path $TOOLS_DIR/cargo-v
    if [ ! -d "${TOOLS_DIR}/verus" ]; then
    git clone https://github.com/ziqiaozhou/verus ${TOOLS_DIR}/verus
    fi
    cd ${TOOLS_DIR}/verus
    git checkout 7c4a5274a4d74522f3965eb038bb7e22fa5eebef
    cd source
    source ../tools/activate
    if [ ! -f "${TOOLS_DIR}/verus/source/z3" ]; then
    ./tools/get-z3.sh
    fi
     vargo build --release
)

echo "add igvm deps"
(
    python3 -m pip install frozendict
    git clone https://github.com/ziqiaozhou/igvm-tooling $TOOLS_DIR/igvm -b verismo-igvm
    cd "$TOOLS_DIR/igvm" && touch src/__init__.py
    if [ ! -f $TOOLS_DIR/venv ]; then
    python3 -m venv $TOOLS_DIR/venv
    fi
    source $TOOLS_DIR/venv/bin/activate && python3 -m pip install src/
)

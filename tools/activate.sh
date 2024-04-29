# Determine the directory that this script is in
if [ "$BASH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
elif [ "$ZSH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${(%):-%N}" )" >/dev/null 2>&1 && pwd )"
else
  echo "Unknown shell; exiting."
  return 1
fi

TOOLS_DIR=$SCRIPT_DIR

echo "submodule init"
(
  git submodule update --init $TOOLS_DIR/verus
  git submodule update --init $TOOLS_DIR/verusfmt
  git submodule update --init $TOOLS_DIR/igvm || true
  git submodule update --init $TOOLS_DIR/../deps/hacl-packages
)
echo "init vstd"
(
  cd "$TOOLS_DIR/../source/vstd/" || exit 1
  ln -s ../../tools/verus/source/vstd src
  cp "lib.rs" "src/"
)

echo "building verus-rustc."
(
    cd "$TOOLS_DIR/verus-rustc" || exit 1
    cargo build --release || exit 1
) || return 1

echo "building verus (slow)..."
(
  cd "$TOOLS_DIR/verus/source" && tools/get-z3.sh && source ../tools/activate && vargo build --release || exit 1
)

echo "building verusfmt."
(
    cd "$TOOLS_DIR/verusfmt" || exit 1
    cargo build --release || exit 1
) || return 1

echo "add igvm deps"
(
    cd "$TOOLS_DIR/igvm" && touch src/__init__.py && sudo apt install acpica-tools && python3 -m pip install frozendict && python3 -m pip install src/
)
export PATH="$SCRIPT_DIR/vargo/target/release:$TOOLS_DIR/verusfmt/target/release:$PATH"

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
    VERUS_REV=a413824dd7c20fe0f72ce988acafb60767fd88e6 cargo install --path $TOOLS_DIR/verus-rustc
) || return 1

echo "add igvm deps"
(
    python3 -m pip install frozendict
    git clone https://github.com/ziqiaozhou/igvm-tooling $TOOLS_DIR/igvm -b verismo-igvm
    cd "$TOOLS_DIR/igvm" && touch src/__init__.py && python3 -m pip install src/
)
export PATH="$SCRIPT_DIR/vargo/target/release:$TOOLS_DIR/verusfmt/target/release:$PATH"

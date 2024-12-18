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
  cargo install --path $TOOLS_DIR/cargo-v
  cargo install --path $TOOLS_DIR/verus-rustc
  cargo v prepare-verus
  curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.4.3/verusfmt-installer.sh | sh
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

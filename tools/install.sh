curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
sudo apt-get install build-essential ninja-build libclang-dev libelf-dev qemu-system podman gcc-9 cmake bison flex unzip
sudo apt install pip
#!/bin/bash
cargo install --git https://github.com/microsoft/verismo/ --rev 28dc242 cargo-v
cargo v prepare-verus
cargo install cargo-run-script
curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/download/v0.4.3/verusfmt-installer.sh | sh


#!/bin/bash
sudo apt-get install build-essential ninja-build libclang-dev libelf-dev qemu-system podman gcc-9 cmake bison flex unzip
sudo apt install pip
builtin=`cargo metadata --format-version 1 | jq -r '.packages[] | select(.name == "builtin") | .targets[].src_path'`
verus=`dirname $builtin`/../../../
verus=`realpath $verus`
export VERUS_PATH=$verus
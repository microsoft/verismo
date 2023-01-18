#!/bin/bash

# powershell.exe -File scripts/upload_titan.ps1 
# workplace/sandbox-wasm-snp/target/target/debug/monito
current_script_path=$(realpath "$0")
DIR=$(dirname $current_script_path)
# echo $OBJECT
/mnt/c/WINDOWS/System32/WindowsPowerShell/v1.0/powershell.exe -File ${DIR}/upload.ps1 -source $(realpath $1) -todir verismo/
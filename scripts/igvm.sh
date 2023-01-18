#!/bin/bash
IGVMGEN=/root/snp/verismo/igvm/igvm/igvmgen.py
python3  $IGVMGEN  -k target/target/debug/monitor_mod -o verismo.bin -vtl=2 -append "root=/dev/sda rw debugpat" -inform verismo -boot_mode x64 -pgtable_level 4 -vmpl2_kernel  /root/snp/out/vmpl2/sm/arch/x86/boot/bzImage
IGVMGEN ?= tools/igvm/igvm/igvmgen.py
RELEASE ?= release
DEBUG ?= debug
IMAGE ?= verismo.bin
TARGET_DIR = ${CURDIR}/legacy/source/target/target/
CMD ?= root=/dev/sda rw debugpat
LINUX_OUT= ${CURDIR}/legacy/richos/target
LINUX ?= ${CURDIR}/legacy/richos/target/arch/x86/boot/bzImage
LINUX_HEADER_DIR=$(realpath $(LINUX_OUT))/mod
LINUX_CONFIG = legacy/richos/kernel/config-richos

default: verifyonly

debugbuild: buildonly fs
	sh ${TARGET_DIR}/${DEBUG}/igvm.sh

verify: verifyonly fs
	sh ${TARGET_DIR}/${RELEASE}/igvm.sh

verifyonly:
	cd legacy/source/verismo_main &&\
	(cargo verus build --release 1> verus-stderr.log)


${CURDIR}/legacy/source/target/target/release/verismo_main:
	verifyonly

${CURDIR}/legacy/source/target/target/${DEBUG}/verismo_main: buildonly

buildonly:
	cd legacy/source/verismo_main && cargo verus build --release


$(LINUX_OUT):
	mkdir -p $(LINUX_OUT)

$(LINUX_OUT)/.config: $(LINUX_OUT)
	mkdir -p $(LINUX_OUT)
	cp ${LINUX_CONFIG} $(LINUX_OUT)/.config

${CURDIR}/legacy/richos/snplinux:
	git clone  https://github.com/ziqiaozhou/linux --depth 1 -b vmpl2/verismo-rebase legacy/richos/snplinux
	cd legacy/richos/snplinux
	git checkout a03a1933bc8aa6bac68c707b2fd3978eb16aedeb
	cd ../../

$(LINUX): ${CURDIR}/legacy/richos/snplinux/ $(LINUX_OUT)/.config
	cd legacy/richos/snplinux/ && make O=$(LINUX_OUT) CC=gcc-9 -j && make O=$(LINUX_OUT) INSTALL_MOD_PATH=$(LINUX_HEADER_DIR) modules_install

kernel: $(LINUX)

driver: kernel
	cd legacy/richos/module && make

fs: driver
	make -C legacy/richos/fs test-fs/verismo.vhdx

clean:
	cd legacy/source && cargo clean


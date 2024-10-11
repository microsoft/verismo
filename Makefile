IGVMGEN ?= tools/igvm/igvm/igvmgen.py
RELEASE ?= release
DEBUG ?= debug
IMAGE ?= verismo.bin
TARGET_DIR = ${CURDIR}/source/target/target/
CMD ?= root=/dev/sda rw debugpat
LINUX_OUT= ${CURDIR}/richos/target
LINUX ?= ${CURDIR}/richos/target/arch/x86/boot/bzImage
LINUX_HEADER_DIR=$(realpath $(LINUX_OUT))/mod
LINUX_CONFIG = richos/kernel/config-richos

default: verifyonly

debugbuild: buildonly fs
	sh ${TARGET_DIR}/${DEBUG}/igvm.sh

verify: verifyonly fs
	sh ${TARGET_DIR}/${RELEASE}/igvm.sh

verifyonly:
	cd source/verismo_main &&\
	(cargo verify --release 1> verus-stderr.log)


${CURDIR}/source/target/target/release/verismo_main:
	verifyonly

${CURDIR}/source/target/target/${DEBUG}/verismo_main: buildonly

buildonly:
	cd source/verismo_main && cargo verify --release --feature noverify


$(LINUX_OUT):
	mkdir -p $(LINUX_OUT)

$(LINUX_OUT)/.config: $(LINUX_OUT)
	mkdir -p $(LINUX_OUT)
	cp ${LINUX_CONFIG} $(LINUX_OUT)/.config

${CURDIR}/richos/snplinux:
	git clone  https://github.com/ziqiaozhou/linux --depth 1 -b vmpl2/verismo-rebase richos/snplinux
	cd richos/snplinux
	git checkout a03a1933bc8aa6bac68c707b2fd3978eb16aedeb
	cd ../../

$(LINUX): ${CURDIR}/richos/snplinux/ $(LINUX_OUT)/.config
	cd richos/snplinux/ && make O=$(LINUX_OUT) CC=gcc-9 -j && make O=$(LINUX_OUT) INSTALL_MOD_PATH=$(LINUX_HEADER_DIR) modules_install

kernel: $(LINUX)

driver: kernel
	cd richos/module && make

fs: driver
	make -C richos/fs test-fs/verismo.vhdx

upload: $(IMAGE)
	sh scripts/upload.sh $(IMAGE)

clean:
	cd source && cargo clean


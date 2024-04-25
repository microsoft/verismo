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

debugbuild: buildonly fs
	sh ${TARGET_DIR}/${DEBUG}/igvm.sh

verify: verifyonly fs
	sh ${TARGET_DIR}/${RELEASE}/igvm.sh

verifyonly:
	cd source/verismo_main &&\
	(cargo build --release 1> verus-stderr.log)


${CURDIR}/source/target/target/release/verismo_main:
	verifyonly

${CURDIR}/source/target/target/${DEBUG}/verismo_main: buildonly

buildonly:
	cd source/verismo_main && cargo build --features noverify 


$(LINUX_OUT):
	mkdir -p $(LINUX_OUT)

$(LINUX_OUT)/.config: $(LINUX_OUT)
	mkdir -p $(LINUX_OUT)
	cp ${LINUX_CONFIG} $(LINUX_OUT)/.config

$(LINUX): richos/snplinux/ $(LINUX_OUT)/.config
	cd richos/snplinux/ && make O=$(LINUX_OUT) -j && make O=$(LINUX_OUT) INSTALL_MOD_PATH=$(LINUX_HEADER_DIR) modules_install

kernel: $(LINUX)

driver: kernel
	cd richos/module && make

fs: driver
	make -C richos/fs test-fs/verismo.vhdx

upload: $(IMAGE)
	sh scripts/upload.sh $(IMAGE)

clean:
	cd source && cargo clean
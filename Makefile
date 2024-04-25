IGVMGEN ?= tools/igvm/igvm/igvmgen.py
profile ?= release
IMAGE ?= verismo.bin
TARGET_DIR = ${CURDIR}/source/target/target/${profile}
TMP_IMAGE = ${TARGET_DIR}/verismo-rust.bin
target ?= ${TARGET_DIR}/verismo_main
CMD ?= root=/dev/sda rw debugpat
LINUX_OUT= ${CURDIR}/richos/target
LINUX ?= ${CURDIR}/richos/target/arch/x86/boot/bzImage
LINUX_HEADER_DIR=$(realpath $(LINUX_OUT))/mod
IGVM = ${TARGET_DIR}/igvm.sh
LINUX_CONFIG = richos/kernel/config-richos

all: build image fs

build: ${target}

verify: verifyonly image fs

verifyonly:
	cd source/verismo_main && (cargo build --release 2>&2 | tee -a verus-stderr.log)


${target}:
	cd source/verismo_main && cargo build --features noverify

${IGVM}: ${target}

${TMP_IMAGE}: ${IGVM}
	sh ${IGVM}

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

$(IMAGE):
	cp ${TMP_IMAGE} $(IMAGE)

image: $(IMAGE)

upload: $(IMAGE)
	sh scripts/upload.sh $(IMAGE)

clean:
	cd source && cargo clean
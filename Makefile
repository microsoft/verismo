IGVMGEN ?= tools/igvm/igvm/igvmgen.py
profile ?= release
IMAGE ?= verismo.bin
TARGET_DIR = source/target/target/${profile}
TMP_IMAGE = ${TARGET_DIR}/verismo-rust.bin
target ?= ${TARGET_DIR}/verismo_main
CMD ?= root=/dev/sda rw debugpat
LINUX ?= /root/snp/out/vmpl2/sm/arch/x86/boot/bzImage
LINUX_OUT=../out/vmpl2/sm
LINUX_HEADER_DIR=$(realpath $(LINUX_OUT))/mod
IGVM = ${TARGET_DIR}/igvm.sh

all: build image fs

build: ${target}

verify: verifyonly image fs

verifyonly:
	cd source/verismo_main && cargo build --release


${target}:
	cd source/verismo_main && cargo build --features noverify --release

${IGVM}: ${target}

${TMP_IMAGE}: ${IGVM}
	sh ${IGVM}

$(LINUX): ../snplinux/
	cd ../snplinux && make O=$(LINUX_OUT) -j && make O=$(LINUX_OUT) INSTALL_MOD_PATH=$(LINUX_HEADER_DIR) modules_install

kernel: ../snplinux/
	cd ../snplinux && make O=$(LINUX_OUT) -j && make O=$(LINUX_OUT) INSTALL_MOD_PATH=$(LINUX_HEADER_DIR) modules_install

driver: kernel
	cd richos/module && make

fs: driver
	make -C richos/fs test-fs/verismo.vhdx

#$(IMAGE): $(target) $(LINUX) kernel
#	python3  ${IGVMGEN}  \
#		-k $(target) \
#		-o $(IMAGE) -vtl=2 -append "${CMD}"\
# 		-inform verismo \
#		-boot_mode x64 \
#		-pgtable_level 4\
#		-vmpl2_kernel  $(LINUX)

$(IMAGE):
	cp ${TMP_IMAGE} $(IMAGE)

image: $(IMAGE)

upload: $(IMAGE)
	sh scripts/upload.sh $(IMAGE)

clean:
	cd source && cargo clean
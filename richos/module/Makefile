obj-m += verismo.o
TARGET?=5.11*
EXTRA_CFLAGS += -fno-pie
ccflags-y += -DDEBUG=1 -fno-pie
LINUX_HEADER_DIR ?= /root/snp/out/vmpl2/sm/mod
KDIR := $(LINUX_HEADER_DIR)/lib/modules/*/build

all:
	make -C $(KDIR) M=$(PWD) modules 
	cp verismo.ko ../fs/test-fs/verismo/files/verismo/

clean:
	make -C $(KDIR) M=$(PWD) clean

format:
	clang-format-12 -style file -i *.c

format-check:
	clang-format-12 -style file -n -Werror *.c

.PHONY: clean

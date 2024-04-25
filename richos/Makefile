all:
	make -C fs test-fs/benchmark.vhd
	make -C fs test-fs/verismo.vhd
	make -C module TARGET=5.11.0-rc5+
	make -C user DIR=$(PWD)/user

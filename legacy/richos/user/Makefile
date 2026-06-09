DOCKER_IMAGE?=test-fs/verismo
out=decode_report
DIR?=${PWD}
all:
	docker run -it -v ${DIR}:/usr/verismo/:rw -w /usr/verismo/ ${DOCKER_IMAGE}  make local
	cp ${out} ../fs/test-fs/verismo/files/verismo/
local:
	gcc user_report.c report.c -o ${out}

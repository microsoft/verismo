FILES-verismo:=
FILES-verismo+=$(CURDIR)/../module/verismo.ko
FILES-verismo+=$(CURDIR)/../user

test-fs/%.vhdx: test-fs/% 
	for f in $(FILES-verismo) ; do echo $$f && mkdir -p $</files/verismo/ && cp -r $$f $</files/verismo/; done;
	sh gen.sh $<

test-fs/verismo.vhdx: $(CURDIR)/../module/verismo.ko $(CURDIR)/../user
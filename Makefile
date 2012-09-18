PROJECT_NAME=coq-compile

all: lib-update
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	@ git archive HEAD -o $(PROJECT_NAME).tgz

lib-update: coq-ext-lib
	@ (cd coq-ext-lib; git pull -u; $(MAKE))

coq-ext-lib:
	./tools/setup.sh

html:
	$(MAKE) -C src html

.dir-locals.el: tools/setup.sh
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el > .dir-locals.el

.PHONY: all clean dist
.PHONY: lib-update

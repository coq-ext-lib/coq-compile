PROJECT_NAME=coq-compile

all: compiler

compiler: lib-update
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean
	$(MAKE) -C test clean
	@ rm -Rf lib bin/*.native

check: compiler
	$(MAKE) -C test

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

.PHONY: all compiler check clean dist
.PHONY: lib-update

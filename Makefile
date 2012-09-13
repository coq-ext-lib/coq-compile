.PHONY: all clean dist

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
	./setup.sh

.PHONEY: lib-update
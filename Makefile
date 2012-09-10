.PHONY: all clean dist

PROJECT_NAME=coq-compile

all: coq-ext-lib
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	@ git archive HEAD -o $(PROJECT_NAME).tgz

lib-update:
	@ (cd coq-ext-lib; git pull -u; $(MAKE))

coq-ext-lib:
	./setup.sh

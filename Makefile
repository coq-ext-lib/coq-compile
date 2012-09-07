.PHONY: all clean dist

PROJECT_NAME=coq-compile

all: coq-ext-lib
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	hg archive -t tgz $(PROJECT_NAME).tgz

coq-ext-lib:
	./setup.sh

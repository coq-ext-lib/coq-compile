all: compiler

.PHONEY: runtime compiler coq coq-lib

clean:
	$(MAKE) -C coq clean
	$(MAKE) -C lib clean
	$(MAKE) -C rt clean
	$(MAKE) -C ml clean

coq: coq-lib
	$(MAKE) -C coq

coq-lib:
	$(MAKE) -C lib

runtime: coq
	$(MAKE) -C rt

compiler: coq runtime
	$(MAKE) -C ml

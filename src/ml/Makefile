EXTLIB_R := -R ../../coq-ext-lib/theories ExtLib

all: CoqCpsKSemantics.ml CoqCompile.ml
	@ ocamlbuild -lib unix all.otarget

coq:
	$(MAKE) -C ../coq

Extraction.vo: Extraction.v coq
	@ coqc $(EXTLIB_R) -R ../coq CoqCompile Extraction

CoqCpsKSemantics.ml: Extraction.vo
CoqCompile.ml: Extraction.vo

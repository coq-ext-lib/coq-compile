EXTLIB_R := -R ../../coq-ext-lib/theories ExtLib

all: CoqCpsKSemantics.ml CoqCompile.ml
	@ ocamlbuild -lib unix all.otarget
	@ mkdir -p ../../bin
	@ cp _build/interp.native _build/compile.native ../../bin

clean:
	@ ocamlbuild -clean all.otarget
	@ rm -f *.vo *.glob
	@ rm -f CoqCompile.ml CoqCompile.mli CoqCpsKSemantics.ml CoqCpsKSemantics.mli

coq:
	$(MAKE) -C ../coq

Extraction.vo: Extraction.v coq
	@ echo "Extracting compiler..."
	@ coqc $(EXTLIB_R) -R ../lib CoqIO -R ../coq CoqCompile Extraction

CoqCpsKSemantics.ml: Extraction.vo
CoqCompile.ml: Extraction.vo

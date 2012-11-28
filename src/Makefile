CORE       := Env Lambda Parse CpsCommon Cps CpsK CpsKSemantics Low LLVM \
	      CpsUtil CpsKUtil AlphaEquivCps AlphaEquivCpsK CpsIO \
	      CpsKIO CpsKConvert \
	      Optimize
OPT        := CseCpsK ReduceCpsK AlphaCvtCpsK DeadCodeCpsK
ANALYSIS   := OccurCps AbstractInterpCps # SimpleAnalysis
COMPILE    := ExtractTypes Cps2CpsK CpsK2Cps CodeGen CloConvK CpsK2Low Compile
MODULES    := $(CORE) $(ANALYSIS:%=Analyze/%) $(OPT:%=Opt/%) $(COMPILE)
TESTS      :=
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . CoqCompile -R ../coq-ext-lib/theories ExtLib

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

extraction: coq
	coqc $(ARGS) extraction.v	

compiler: extraction
	cd extraction/; ocamlbuild -lib unix Wrapper.byte

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

admit:
	@ grep -n -e 'admit' -e 'Admitted' -e 'Parameter' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)

html:
	$(MAKE) -f Makefile.coq html

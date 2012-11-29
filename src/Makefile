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
	coqc $(ARGS) Extraction.v	

compiler: extraction
	cd Extraction/; ocamlbuild -lib unix Wrapper.byte

semantics : extraction
	cd Extraction/; ocamlbuild -lib unix CpsKInterpTL.byte

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

runtime:
	$(MAKE) -C Runtime

test: coq compiler runtime
	$(MAKE) -C Test test

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C Runtime clean
	$(MAKE) -C Test clean
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

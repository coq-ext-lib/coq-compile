CORE       := Env Lambda Parse CpsCommon Cps CpsK CpsKExamples CpsKSemantics Low LLVM \
	      CpsUtil CpsKUtil AlphaEquivCps AlphaEquivCpsK \
	      CpsKIO CpsKConvert \
	      Optimize TraceMonad
OPT        := CseCpsK ReduceCpsK AlphaCvtCpsK DeadCodeCpsK CopyPropCpsK \
	      ContificationCpsK
ANALYSIS   := OccurCps AbstractDomains AbstractInterpCpsK CFA0 Reachability
COMPILE    := ExtractTypes Cps2CpsK CpsK2Cps CodeGen CloConvK CpsK2Low Compile
MODULES    := $(CORE) $(ANALYSIS:%=Analyze/%) $(OPT:%=Opt/%) $(COMPILE) $(RUNTIME)
TESTS      := CompileTest
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . CoqCompile -R ../../coq-ext-lib/theories ExtLib

.PHONY: clean runtime test

.coq-done: Makefile.coq
	@ $(MAKE) -f Makefile.coq
	@ touch .coq-done

coq: .coq-done

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

clean: Makefile.coq
	@ rm -f .coq-done
	@ $(MAKE) -f Makefile.coq clean
	@ rm -f Makefile.coq .depend

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

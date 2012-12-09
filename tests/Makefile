COMPILER=../bin/coq-compile
OPT=-O1 --llvm-opt
IO_OPTS=-io --coq-args '-R ../lib CoqIO -R ../coq-ext-lib/theories/ ExtLib'

all: Ident Fact TRFact True False GC HelloWorld

.PHONY: runtime

test: Ident Fact TRFact True False GC HelloWorld
	@echo =============================================
	@echo Running tests
	@echo =============================================
	@echo Running Ident testcase...
	./ident.native -d --Xms=2k
	@echo
	@echo Running Factorial testcase...
	./fact.native -d --Xms=2k
	@echo
	@echo Running Tail-recursive Factorial testcase...
	./trfact.native -d --Xms=2k
	@echo
	@echo Running even 20 testcase...
	./true.native -d --Xms=2k
	@echo
	@echo Running even 21 testcase...
	./false.native -d --Xms=2k
	@echo
	@echo Running gc testcase...
	./gc.native -d --Xms=2k
	@echo
	@echo Running hello world testcase...
	./helloworld.native -d --Xms=8k

test-gc: GC
	./gc.native -d --Xms=4k

runtime:

Ident: runtime Ident.v
	$(COMPILER) $(OPT) -o ident.native Ident.call_ident 

Fact: runtime Fact.v
	$(COMPILER) $(OPT) -o fact.native Fact.fact6

TRFact: runtime Fact.v
	$(COMPILER) $(OPT) -o trfact.native Fact.tr_fact6

True: runtime Even.v
	$(COMPILER) $(OPT) -o true.native Even.true

False: runtime Even.v
	$(COMPILER) $(OPT) -o false.native Even.false

GC: runtime Even.v
	$(COMPILER) $(OPT) -o gc.native Even.gc_test

HelloWorld: runtime HelloWorld.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o helloworld.native HelloWorld.main

IOFact: runtime IOFact.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o iofact.native IOFact.main

IONat: runtime IONat.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o ionat.native IONat.main

Compiler: runtime Compiler.v
	$(COMPILER) $(OPT) -o compiler.native IONat.main
	# ../Extraction/Wrapper.native -O1 -arg "-R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib" -e Compiler.scheme -q -o compiler.ll
	# llvm-link rt.ll compiler.ll -S -o compiler-rt.ll
	# opt -O3 -S compiler-rt.ll -o compiler-opt.ll
	# llc compiler-opt.ll -o compiler-opt.s
	# clang -lrt -g compiler-opt.s shadowstack.o -o compiler.native

clean:
	@ rm -f *.ll *.s *.o *.native *.vo *.glob tmp_extr.* *.bc

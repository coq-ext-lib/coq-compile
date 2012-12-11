COMPILER=../bin/coq-compile
OPT=-O1 --llvm-opt
IO_OPTS=-io --coq-args '-R ../lib CoqIO -R ../coq-ext-lib/theories/ ExtLib'

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

all: Ident Fact TRFact True False GC HelloWorld

Ident: Ident.v
	$(COMPILER) $(OPT) -o ident.native Ident.call_ident 

Fact: Fact.v
	$(COMPILER) $(OPT) -o fact.native Fact.fact6

TRFact: Fact.v
	$(COMPILER) $(OPT) -o trfact.native Fact.tr_fact6

True: Even.v
	$(COMPILER) $(OPT) -o true.native Even.true

False: Even.v
	$(COMPILER) $(OPT) -o false.native Even.false

GC: Even.v
	$(COMPILER) $(OPT) -o gc.native Even.gc_test

HelloWorld: HelloWorld.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o helloworld.native HelloWorld.main

IOFact: IOFact.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o iofact.native IOFact.main

IONat: IONat.v
	$(COMPILER) $(IO_OPTS) $(OPT) -o ionat.native IONat.main

Compiler: Compiler.v
	$(COMPILER) $(OPT) -o compiler.native IONat.main

clean:
	@ rm -f *.ll *.s *.o *.native *.vo *.glob tmp_extr.* *.bc

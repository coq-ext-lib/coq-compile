all: Ident Fact TRFact True False GC HelloWorld

.PHONY: runtime

test: Ident Fact TRFact True False GC HelloWorld
	@echo =============================================
	@echo Running tests
	@echo =============================================
	@echo Running Ident testcase...
	./ident.native -d
	@echo
	@echo Running Factorial testcase...
	./fact.native -d
	@echo
	@echo Running Tail-recursive Factorial testcase...
	./trfact.native -d
	@echo
	@echo Running even 200 testcase...
	./true.native -d
	@echo
	@echo Running even 201 testcase...
	./false.native -d
	@echo
	@echo Running gc testcase...
	./gc.native -d
	@echo
	@echo Running hello world testcase...
	./helloworld.native -d

test-gc: GC
	./gc.native -d --Xms=4k

runtime:
	cp ../Runtime/coqrt.ll coqrt.ll
	cp ../Runtime/shadowstack.o shadowstack.o

Ident: runtime Ident.v
	coqc Ident.v
	../Extraction/Wrapper.byte -O0 -i Ident -t call_ident -o ident.ll
	llvm-link coqrt.ll ident.ll -S -o ident-coqrt.ll
	opt -S ident-coqrt.ll -o ident-opt.ll
	llc ident-opt.ll -o ident-opt.s
	clang -lrt ident-opt.s shadowstack.o -o ident.native

Fact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O0 -i Fact -t fact6 -o fact.ll
	llvm-link coqrt.ll fact.ll -S -o fact-coqrt.ll
	opt -S fact-coqrt.ll -o fact-opt.ll
	llc fact-opt.ll -o fact-opt.s
	clang -lrt fact-opt.s shadowstack.o -o fact.native

TRFact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O0 -i Fact -t tr_fact6 -o trfact.ll
	llvm-link coqrt.ll trfact.ll -S -o trfact-coqrt.ll
	opt -S trfact-coqrt.ll -o trfact-opt.ll
	llc trfact-opt.ll -o trfact-opt.s
	clang -lrt trfact-opt.s shadowstack.o -o trfact.native

True: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O0 -i Even -t true -o true.ll
	llvm-link coqrt.ll true.ll -S -o true-coqrt.ll
	opt -S true-coqrt.ll -o true-opt.ll
	llc true-opt.ll -o true-opt.s
	clang -lrt true-opt.s shadowstack.o -o true.native

False: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O0 -i Even -t false -o false.ll
	llvm-link coqrt.ll false.ll -S -o false-coqrt.ll
	opt -S false-coqrt.ll -o false-opt.ll
	llc false-opt.ll -o false-opt.s
	clang -lrt false-opt.s shadowstack.o -o false.native

GC: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O0 -i Even -t gc_test -o gc.ll
	llvm-link coqrt.ll gc.ll -S -o gc-coqrt.ll
	opt -S gc-coqrt.ll -o gc-opt.ll
	llc gc-opt.ll -o gc-opt.s
	clang -lrt gc-opt.s shadowstack.o -o gc.native

HelloWorld: runtime HelloWorld.v
	coqc -R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib HelloWorld.v
	../Extraction/Wrapper.byte -O0 -io -arg "-R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib" -i HelloWorld -t main -o helloworld.ll
	llvm-link coqrt.ll helloworld.ll -S -o helloworld-coqrt.ll
	opt -S helloworld-coqrt.ll -o helloworld-opt.ll
	llc helloworld-opt.ll -o helloworld-opt.s
	clang -lrt helloworld-opt.s shadowstack.o -o helloworld.native

IOFact: runtime IOFact.v
	coqc -R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib IOFact.v
	../Extraction/Wrapper.byte -O0 -io -arg "-R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib" -i IOFact -t main -o iofact.ll
	llvm-link coqrt.ll iofact.ll -S -o iofact-coqrt.ll
	opt -S iofact-coqrt.ll -o iofact-opt.ll
	llc iofact-opt.ll -o iofact-opt.s
	clang -lrt iofact-opt.s shadowstack.o -o iofact.native

Compiler: runtime Compiler.v
	../Extraction/Wrapper.byte -O0 -arg "-R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib" -e Compiler.scheme -q -o compiler.ll
	llvm-link rt.ll compiler.ll -S -o compiler-rt.ll
	opt -S compiler-rt.ll -o compiler-opt.ll
	llc compiler-opt.ll -o compiler-opt.s
	clang -lrt -g compiler-opt.s shadowstack.o -o compiler.native

clean:
	rm -f *.ll *.s *.o *.native *.vo *.glob tmp_extr.*

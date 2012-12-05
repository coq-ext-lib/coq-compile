all: Ident Fact TRFact True False GC

.PHONY: runtime

test: Ident Fact TRFact True False GC
	echo Running Ident testcase...
	./ident.native -d
	echo Running Factorial testcase...
	./fact.native -d
	echo Running Tail-recursive Factorial testcase...
	./trfact.native -d
	echo Running even 200 testcase...
	./true.native -d
	echo Running even 201 testcase...
	./false.native -d
	echo Runnint gc testcase...
	./gc.native -d

test: Fact
	./fact.native -d

test-gc: GC
	./gc.native -d --Xms=4k

runtime:
	cp ../Runtime/coqrt.ll coqrt.ll
	cp ../Runtime/shadowstack.o shadowstack.o

Ident: runtime Ident.v
	coqc Ident.v
	../Extraction/Wrapper.byte -O2 -i Ident -t call_ident -o ident.ll
	llvm-link coqrt.ll ident.ll -S -o ident-coqrt.ll
	opt -O3 -S ident-coqrt.ll -o ident-opt.ll
	llc ident-opt.ll -o ident-opt.s
	clang ident-opt.s shadowstack.o -o ident.native

Fact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O2 -i Fact -t fact6 -o fact.ll
	llvm-link coqrt.ll fact.ll -S -o fact-coqrt.ll
	opt -O3 -S fact-coqrt.ll -o fact-opt.ll
	llc fact-opt.ll -o fact-opt.s
	clang fact-opt.s shadowstack.o -o fact.native

TRFact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O2 -i Fact -t tr_fact6 -o trfact.ll
	llvm-link coqrt.ll trfact.ll -S -o trfact-coqrt.ll
	opt -O3 -S trfact-coqrt.ll -o trfact-opt.ll
	llc trfact-opt.ll -o trfact-opt.s
	clang trfact-opt.s shadowstack.o -o trfact.native

True: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O2 -i Even -t true -o true.ll
	llvm-link coqrt.ll true.ll -S -o true-coqrt.ll
	opt -O3 -S true-coqrt.ll -o true-opt.ll
	llc true-opt.ll -o true-opt.s
	clang true-opt.s shadowstack.o -o true.native

False: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O2 -i Even -t false -o false.ll
	llvm-link coqrt.ll false.ll -S -o false-coqrt.ll
	opt -O3 -S false-coqrt.ll -o false-opt.ll
	llc false-opt.ll -o false-opt.s
	clang false-opt.s shadowstack.o -o false.native

GC: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O2 -i Even -t gc_test -o gc.ll
	llvm-link coqrt.ll gc.ll -S -o gc-coqrt.ll
	opt -O3 -S gc-coqrt.ll -o gc-opt.ll
	llc gc-opt.ll -o gc-opt.s
	clang gc-opt.s shadowstack.o -o gc.native

Compiler: runtime Compiler.v
#	coqc -R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib Compiler.v
	../Extraction/Wrapper.byte -O2 -e compile.scheme -q -o compiler.ll
	llvm-link rt.ll compiler.ll -S -o compiler-rt.ll
	opt -O3 -S compiler-rt.ll -o compiler-opt.ll
	llc compiler-opt.ll -o compiler-opt.s
	clang -g compiler-opt.s shadowstack.o -o compiler.native

clean:
	rm -f *.ll *.s *.o *.native *.vo *.glob tmp_extr.*

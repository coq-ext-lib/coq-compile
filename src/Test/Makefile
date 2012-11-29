all: Ident Fact True False

test: Ident Fact True False
	echo Running Ident testcase...
	./ident.native
	echo Running Ident testcase...
	./fact.native
	echo Running even 200 testcase...
	./true.native
	echo Running even 201 testcase...
	./false.native

runtime: rt.c
	clang -emit-llvm -S rt.c -o rt.ll

Ident: runtime Ident.v
	coqc Ident.v
	../Extraction/Wrapper.byte -O1 -i Ident -t ident -o ident.ll
	llvm-link rt.ll ident.ll -S -o ident-rt.ll
	opt -O3 -S ident-rt.ll -o ident-opt.ll
	llc ident-opt.ll -o ident-opt.s
	gcc -g ident-opt.s -o ident.native

Fact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O1 -i Fact -t fact -o fact.ll
	llvm-link rt.ll fact.ll -S -o fact-rt.ll
	opt -O3 -S fact-rt.ll -o fact-opt.ll
	llc fact-opt.ll -o fact-opt.s
	gcc -g fact-opt.s -o fact.native

True: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O1 -i Even -t true -o true.ll
	llvm-link rt.ll true.ll -S -o true-rt.ll
	opt -O3 -S true-rt.ll -o true-opt.ll
	llc true-opt.ll -o true-opt.s
	gcc -g true-opt.s -o true.native

False: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O1 -i Even -t false -o false.ll
	llvm-link rt.ll false.ll -S -o false-rt.ll
	opt -O3 -S false-rt.ll -o false-opt.ll
	llc false-opt.ll -o false-opt.s
	gcc -g false-opt.s -o false.native

clean:
	rm -f *.ll *.s *.native *.vo *.glob tmp_extr.*

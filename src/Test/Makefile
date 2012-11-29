all: Ident Fact True False

test: Ident Fact True False
	echo Running Ident testcase...
	./ident.native -d
	echo Running Ident testcase...
	./fact.native -d
	echo Running even 200 testcase...
	./true.native -d
	echo Running even 201 testcase...
	./false.native -d

runtime:
	cp ../Runtime/coqrt.ll coqrt.ll

Ident: runtime Ident.v
	coqc Ident.v
	../Extraction/Wrapper.byte -O1 -i Ident -t ident -o ident.ll
	llvm-link coqrt.ll ident.ll -S -o ident-coqrt.ll
	opt -O3 -S ident-coqrt.ll -o ident-opt.ll
	llc ident-opt.ll -o ident-opt.s
	clang ident-opt.s -o ident.native

Fact: runtime Fact.v
	coqc Fact.v
	../Extraction/Wrapper.byte -O1 -i Fact -t fact -o fact.ll
	llvm-link coqrt.ll fact.ll -S -o fact-coqrt.ll
	opt -O3 -S fact-coqrt.ll -o fact-opt.ll
	llc fact-opt.ll -o fact-opt.s
	clang fact-opt.s -o fact.native

True: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O1 -i Even -t true -o true.ll
	llvm-link coqrt.ll true.ll -S -o true-coqrt.ll
	opt -O3 -S true-coqrt.ll -o true-opt.ll
	llc true-opt.ll -o true-opt.s
	clang true-opt.s -o true.native

False: runtime Even.v
	coqc Even.v
	../Extraction/Wrapper.byte -O1 -i Even -t false -o false.ll
	llvm-link coqrt.ll false.ll -S -o false-coqrt.ll
	opt -O3 -S false-coqrt.ll -o false-opt.ll
	llc false-opt.ll -o false-opt.s
	clang false-opt.s -o false.native

clean:
	rm -f *.ll *.s *.native *.vo *.glob tmp_extr.*

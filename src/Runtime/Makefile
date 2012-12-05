coqrt: coqrt.ll shadowstack.o

.PHONY: clean

coqrt.ll: coqrtbegin.c semispacegc.c
	clang -g -emit-llvm -S -o coqrtbegin.ll coqrtbegin.c
	clang -g -emit-llvm -S -o semispacegc.ll semispacegc.c
	llvm-link -S -o coqrt.ll coqrtbegin.ll semispacegc.ll

shadowstack.o: shadowstack.c
	clang -g -c shadowstack.c

clean:
	rm -f *.ll *.o

coqrt: coqrt.ll shadowstack.o

.PHONY: clean

coqrt.ll: coqrtbegin.c semispacegc.c coqio.c
	clang -emit-llvm -S -o coqrtbegin.ll coqrtbegin.c
	clang -emit-llvm -S -o semispacegc.ll semispacegc.c
	clang -emit-llvm -S -o coqio.ll coqio.c
	llvm-link -o coqrt.ll coqrtbegin.ll semispacegc.ll coqio.ll

shadowstack.o: shadowstack.c
	clang -c shadowstack.c

clean:
	rm -f *.ll *.o

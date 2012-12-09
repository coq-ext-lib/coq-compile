INCLUDEDIR=include
CFLAGS=-g -I$(INCLUDEDIR)
INCLUDES=$(wildcard $(INCLUDEDIR)/*.h)

coqrt: coqrt.ll shadowstack.o

.PHONY: clean

%.ll: %.c $(INCLUDES)
	clang $(CFLAGS) -emit-llvm -S -o $@ $<

coqrt.ll: coqrtbegin.ll coqio.ll data.ll semispacegc.ll
	llvm-link -S -o coqrt.ll coqrtbegin.ll semispacegc.ll coqio.ll data.ll

shadowstack.o: shadowstack.c $(INCLUDES)
	clang $(CFLAGS) -c shadowstack.c

clean:
	rm -f *.ll *.o

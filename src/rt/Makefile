INCLUDEDIR=include
CFLAGS=-g -I$(INCLUDEDIR)
INCLUDES=$(wildcard $(INCLUDEDIR)/*.h)

all: setup

coqrt: coqrt.bc shadowstack.o

.PHONY: clean

%.ll: %.c $(INCLUDES)
	clang $(CFLAGS) -emit-llvm -S -o $@ $<

coqrt.ll: coqrtbegin.ll coqio.ll data.ll semispacegc.ll
	llvm-link -S -o coqrt.ll coqrtbegin.ll semispacegc.ll coqio.ll data.ll

coqrt.bc: coqrt.ll
	llvm-as -o coqrt.bc coqrt.ll

shadowstack.o: shadowstack.c $(INCLUDES)
	clang $(CFLAGS) -c shadowstack.c

clean:
	@ rm -f *.ll *.o *.bc

setup: coqrt
	@ mkdir -p ../../lib
	@ cp shadowstack.o ../../lib
	@ cp coqrt.bc ../../lib

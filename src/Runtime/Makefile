all: coqrt.ll

%.ll: %.c
	clang -emit-llvm -S -o $@ $<

clean:
	rm -f *.ll

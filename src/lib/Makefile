all: IO.vo IO_ml.vo IO_compile.vo
	@ mkdir -p ../../lib
	@ cp IO.vo IO_ml.vo IO_compile.vo ../../lib

clean:
	@ rm -f *.vo *.glob

IO.vo: IO.v
	coqc -R . CoqIO -R ../../coq-ext-lib/theories ExtLib IO

IO_ml.vo: IO_ml.v IO.vo
	coqc -R . CoqIO -R ../../coq-ext-lib/theories ExtLib IO_ml

IO_compile.vo: IO_compile.v IO.vo
	coqc -R . CoqIO -R ../../coq-ext-lib/theories ExtLib IO_compile

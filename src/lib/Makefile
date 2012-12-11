all: IO.vo
	@ mkdir -p ../../lib
	@ cp IO.vo ../../lib

clean:
	@ rm -f *.vo *.glob

IO.vo: IO.v
	coqc -R . CoqIO -R ../../coq-ext-lib/theories ExtLib IO

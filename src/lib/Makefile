all: IO.vo
	@ cp IO.vo ../../lib

clean:
	@ rm -f *.vo *.glob

IO.vo: IO.v
	coqc -R . CoqIO -R ../../coq-ext-lib/theories ExtLib IO

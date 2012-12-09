all: IO.vo
	cp IO.vo ../../lib

IO.vo: IO.v
	coqc -R ../../coq-ext-lib/theories ExtLib IO

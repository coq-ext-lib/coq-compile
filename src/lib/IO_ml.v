Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import String.
Extraction Blacklist String List.
Require CoqIO.IO.

(** Since we're going to extract to Ocaml, we need to set up different
 ** extractions for the IO primitives
 **)
Extract Constant IO.IO "'t" => " 't CoqIO.io ".
Extract Inductive IO.std => "CoqIO.std" [ "CoqIO.StdOut" "CoqIO.StdErr" ].
Extract Inlined Constant IO.IO_bind => "CoqIO.io_bind".
Extract Inlined Constant IO.IO_ret => "CoqIO.io_ret".
Extract Inlined Constant IO.IO_printChar => "CoqIO.io_printChar".
Extract Inlined Constant IO.IO_printCharF => "CoqIO.io_printCharF".
Extract Inlined Constant IO.IO_read => "CoqIO.io_read".
Extraction Language Ocaml.
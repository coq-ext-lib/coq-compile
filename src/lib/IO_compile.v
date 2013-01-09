Require Import CoqIO.IO.
(** Extraction Hints **)
Extract Constant IO "t" => "io t".
Extract Constant IO_bind => "io_bind".
Extract Constant IO_ret => "io_ret".
Extract Constant IO_printChar => "io_printChar".
Extract Constant IO_printCharF => "io_printCharF".
Extract Constant IO_read => "io_read".

type std = StdOut | StdErr

type 'a io

val io_bind : 'a io -> ('a -> 'b io) -> 'b io

val io_ret : 'a -> 'a io

val io_printChar : char -> unit io

val io_printCharF : std -> char -> unit io

val io_read : char io

(** Since ocaml internalizes IO **)
val run_io : 'a io -> 'a 

val make_io : (unit -> 'a) -> 'a io

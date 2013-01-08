type std = StdOut | StdErr

type 'a io = unit -> 'a

let io_bind (c : 'a io) (f : 'a -> 'b io) : 'b io =
  fun y -> 
    let x = c () in
    f x y

let io_ret (x : 'a) : 'a io = fun _ -> x

let io_printChar (c : char) : unit io =
  fun _ -> print_char c

let io_printCharF (s : std) (c : char) : unit io =
  fun _ -> 
    match s with
      | StdOut -> print_char c
      | StdErr -> prerr_char c

let io_read : char io =
  fun _ ->
    input_char stdin
  
let run_io c = c ()

let make_io c = c

open String;;
open Util;;

let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [-o output file] [-i Coq module] [-t Coq term]"
let output = ref "out.ll"
let input = ref (None: string option)
let term = ref (None: string option)
let opt = ref (Compile.Compile.Opt.coq_O0)
let io = ref false

let params =
  [("-o" , Arg.String (fun s -> output := s), "<file> Place output into <file>");
   ("-i", Arg.String (fun s -> input := Some s),
      "<coq module name> Coq module where term is defined");
   ("-t", Arg.String (fun s -> term := Some s),
      "<coq term> Coq term to extract");
   ("-O0", Arg.Unit (fun () -> opt := Compile.Compile.Opt.coq_O0), " Optimizer Level 0 (default)");
   ("-O1", Arg.Unit (fun () -> opt := Compile.Compile.Opt.coq_O1), " Optimizer Level 1");
   ("-io", Arg.Unit (fun () -> io := true), " Wrapping with IO monad")
  ];;

let anon = (fun x -> failwith "Bad argument")

let _ = 
  Arg.parse params anon usage_string;
  match !input, !term with
    | Some s, Some t -> Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
      (let source = extract s t in
       print_string source;
       match Compile.topcompile !opt !io (explode source) with
         | Compile.Inl s -> print_endline (implode s) 
	 | Compile.Inr assembly -> 
	   let out_ref = open_out !output in
	   output_string out_ref (implode assembly))
    | _, _ -> print_string "Missing input or term.\n"


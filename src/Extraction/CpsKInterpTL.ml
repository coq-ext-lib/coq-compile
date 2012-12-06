open String;;
open Util;;

let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [-o output file] [-i Coq module] [-t Coq term]"
let output = ref "out.ll"
let input = ref (None: string option)
let term = ref (None: string option)
let fuel = ref 100
let comp_args = ref ""
let cc = ref false
let io = ref false

let params =
  [("-o" , Arg.String (fun s -> output := s), "<file> Place output into <file>");
   ("-i", Arg.String (fun s -> input := Some s),
      "<coq module name> Coq module where term is defined");
   ("-t", Arg.String (fun s -> term := Some s),
      "<coq term> Coq term to extract");
   ("-n", Arg.String (fun s -> fuel := int_of_string s),
      "<number> Amount of fuel");
   ("-cc", Arg.Unit (fun () -> cc := true), "Closure convert before running");
   ("-io", Arg.Unit (fun () -> io := true), "Wrapping with IO monad");
   ("-arg", Arg.String (fun s -> comp_args := !comp_args ^ " " ^ s), " Parameters to pass to coqc")
  ];;

let anon = (fun x -> failwith "Bad argument")

let _ = 
  Arg.parse params anon usage_string;
  match !input, !term with
    | Some s, Some t -> Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
      (let source = extract !comp_args s t in
       print_string source;
       match CpsKSemantics.topeval (make_N !fuel) !io !cc (explode source) with
         | CpsKSemantics.Inl s -> print_endline (implode s) 
      	 | CpsKSemantics.Inr ((vs, heap), mops) ->
           let vstr = List.fold_left (fun acc v -> List.append acc (CpsKSemantics.val2str v)) [] vs in
		       let out_ref = open_out !output in
	         output_string out_ref (implode vstr))
    | _, _ -> print_string "Missing input or term.\n"


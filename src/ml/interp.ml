open String;;

let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [-o output file] [-i Coq module] [-t Coq term]"
let output = ref "out.ll"
let input = ref (None: string option)
let term = ref (None: string option)
let fuel = ref 100
let comp_args = ref ""
let cc = ref false
let io = ref false
let print = ref false

let params =
  [("-o" , Arg.String (fun s -> output := s), "<file> Place output into <file>");
   ("-i", Arg.String (fun s -> input := Some s),
      "<coq module name> Coq module where term is defined");
   ("-t", Arg.String (fun s -> term := Some s),
      "<coq term> Coq term to extract");
   ("-n", Arg.String (fun s -> fuel := int_of_string s),
      "<number> Amount of fuel");
   ("-cc", Arg.Unit (fun () -> cc := true), "Closure convert before running");
   ("-print", Arg.Unit (fun () -> print := true), "Print before running");
   ("-io", Arg.Unit (fun () -> io := true), "Wrapping with IO monad");
   ("-arg", Arg.String (fun s -> comp_args := !comp_args ^ " " ^ s), " Parameters to pass to coqc")
  ];;

let anon = (fun x -> failwith "Bad argument")

let _ = 
  Arg.parse params anon usage_string;
  match !input, !term with
    | Some s, Some t -> 
      begin
	Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
	let source = Extraction.extract !comp_args s t in
	let coq_source = CoqUtil.explode source in
	match CoqCpsKSemantics.topeval (CoqUtil.make_N !fuel) !io !cc coq_source with
          | (p,CoqCpsKSemantics.Inl s) ->
	    if !print then print_endline (CoqUtil.implode p) ;
	    print_string "\nERROR------------------------\n" ;
	    print_endline (CoqUtil.implode s) 
      	  | (p,CoqCpsKSemantics.Inr ((vs, heap), mops)) ->
	    if !print then print_endline (CoqUtil.implode p) ;
            let vstr = List.fold_left (fun acc v -> List.append acc (CoqCpsKSemantics.val2str v)) [] vs in
	    let out_ref = open_out !output in
	    output_string out_ref (CoqUtil.implode vstr) ;
	    print_string "\nSUCCESS!!!!!!!!!!!!!!!!!!!!!!!!!!!\n" 
      end
    | _, _ -> print_string "Missing input or term.\n"


open String;;
open Util;;

let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [-o output file] [-i Coq module] [-t Coq term]"
let output = ref "out.ll"
let input = ref (None: string option)
let term = ref (None: string option)
let opt = ref (Compile.Compile.Opt.coq_O0)
let io = ref false
let dupdate = ref false
let comp_args = ref ""
let lit = ref (None : string option)
let quiet = ref false
let stop = ref Compile.Compile.LLVM_stop

let params =
  [("-o" , Arg.String (fun s -> output := s), "<file> Place output into <file>");
   ("-i", Arg.String (fun s -> input := Some s),
      "<coq module name> Coq module where term is defined");
   ("-t", Arg.String (fun s -> term := Some s),
      "<coq term> Coq term to extract");
   ("-e", Arg.String (fun s -> lit := Some s), "file to read for the extracted term");
   ("-q", Arg.Unit (fun () -> quiet := true), "don't print the extracted string");
   ("-O0", Arg.Unit (fun () -> opt := Compile.Compile.Opt.coq_O0), " Optimizer Level 0 (default)");
   ("-O1", Arg.Unit (fun () -> opt := Compile.Compile.Opt.coq_O1), " Optimizer Level 1");
   ("-O2", Arg.Unit (fun () -> opt := Compile.Compile.Opt.coq_O2), " Optimizer Level 2");
   ("-io", Arg.Unit (fun () -> io := true), " Wrapping with IO monad");
   ("-stop", Arg.String (fun s -> if s = "llvm" then stop := Compile.Compile.LLVM_stop else 
			          if s = "low" then stop := Compile.Compile.Low_stop else
				  if s = "cc" then stop := Compile.Compile.Clo_stop else
				  assert false), "Stage to stop at");
   ("-dupdate", Arg.Unit (fun () -> dupdate := true), " Use destructive updates");
   ("-arg", Arg.String (fun s -> comp_args := !comp_args ^ " " ^ s), " Parameters to pass to coqc")
 ];;

let anon = (fun x -> failwith "Bad argument")

let compile_from_str source =
  if not !quiet then print_string source ;
  match Compile.topcompile !opt !io (explode source) !stop !dupdate with
    | Compile.Inl s -> print_endline (implode s) 
    | Compile.Inr assembly -> 
	let out_ref = open_out !output in
	  output_string out_ref (implode assembly)

let _ = 
  Arg.parse params anon usage_string;
  match !lit with
    | None ->
	begin
	  match !input, !term with
	    | Some s, Some t ->
		begin
		  Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
		  let source = extract !comp_args s t in
		  compile_from_str source
		end
	    | _, _ -> print_string "Missing input or term.\n"
	end
    | Some file ->
	let scheme_file = open_in file in
	let length = in_channel_length scheme_file in
	let extracted_source = create length in
	really_input scheme_file extracted_source 0 length;
	compile_from_str extracted_source


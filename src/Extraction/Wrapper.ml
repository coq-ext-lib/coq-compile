open String;;

(* Our old friend... string implode/explode - this is from the OCaml bug
   tracker *)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

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

let extract (m: string) (t: string) =
  let extr = open_out "tmp_extr.v" in
  Printf.fprintf extr "Require %s.\nExtraction Language Scheme.\nRecursive Extraction %s.%s.\n"
    m m t;
  flush extr;
  (* Run the extraction, then chop off the first 4 lines because
     the parser can't handle them *)
  let status = Unix.system "coqc tmp_extr.v | tail -n +4 > tmp_extr.scheme" in
  match status with
    | Unix.WEXITED 0 -> 
      let scheme_file = open_in "tmp_extr.scheme" in
      let length = in_channel_length scheme_file in
      let extracted_source = create length in
      really_input scheme_file extracted_source 0 length;
      extracted_source;
    | _ -> failwith "Extraction failed."

(*
let _ = 
  Arg.parse params anon usage_string;
  match !input, !term with
    | Some s, Some t -> Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
      (let source = extract s t in
       print_string source;
       match Compile.Compile.stringToAssembly (Compile.S (Compile.O)) !opt (explode source) with
         | Compile.Inl s -> print_endline (implode s) 
	 | Compile.Inr assembly -> 
	   let out_ref = open_out !output in
	   output_string out_ref (implode assembly))
    | _, _ -> print_string "Missing input or term.\n"
*)

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


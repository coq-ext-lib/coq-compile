open String;;
open Util;;

let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [-o output file] [-i Coq module] [-t Coq term]"
let output = ref "out.ll"
let input = ref (None: string option)
let term = ref (None: string option)
let fuel = ref 100

let params =
  [("-o" , Arg.String (fun s -> output := s), "<file> Place output into <file>");
   ("-i", Arg.String (fun s -> input := Some s),
      "<coq module name> Coq module where term is defined");
   ("-t", Arg.String (fun s -> term := Some s),
      "<coq term> Coq term to extract");
   ("-n", Arg.String (fun s -> fuel := int_of_string s),
      "<number> Amount of fuel")
  ];;

let anon = (fun x -> failwith "Bad argument")

let rec make_nat n =
  if n > 0 then CpsKSemantics.S (make_nat (n - 1)) else CpsKSemantics.O

let _ = 
  Arg.parse params anon usage_string;
  match !input, !term with
    | Some s, Some t -> Printf.printf "Input: %s\nTerm: %s\nOutput: %s\n----\n" s t !output;
      (let source = extract s t in
       print_string source;
       match CpsKSemantics.topeval (make_nat !fuel) (explode source) with
         | CpsKSemantics.Inl s -> print_endline (implode s) 
      	 | CpsKSemantics.Inr ((vs, heap), mops) ->
           let vstr = List.fold_left (fun acc v -> List.append acc (CpsKSemantics.val2str v)) [] vs in
		       let out_ref = open_out !output in
	         output_string out_ref (implode vstr))
    | _, _ -> print_string "Missing input or term.\n"


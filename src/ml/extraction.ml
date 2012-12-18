open String;;

let extract (args : string) (m: string) (t: string) =
  let (coq_name, coq_file) = 
    Filename.open_temp_file "extr_" ".v"
  in
  Printf.fprintf coq_file "Require %s.\nExtraction Language Scheme.\nRecursive Extraction %s.%s.\n" m m t;
  close_out coq_file ;
  (* Run the extraction, then chop off the first 4 lines because
     the parser can't handle them *)
(*  let status = Unix.system "coqc -R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib tmp_extr.v | tail -n +4 > tmp_extr.scheme" in *)
  let (scheme_name, scheme_file) = 
    Filename.open_temp_file "extr_" ".scheme"
    (* open_in "tmp_extr.scheme" *)
  in
  close_out scheme_file ;
  let status = Unix.system (Printf.sprintf "coqc %s %s | tail -n +4 > %s" args  coq_name scheme_name) in 
  match status with
    | Unix.WEXITED 0 -> 
      let scheme_file = open_in scheme_name in
      let length = in_channel_length scheme_file in
      let extracted_source = create length in
      really_input scheme_file extracted_source 0 length ;
      extracted_source;
    | _ -> failwith "Extraction failed."

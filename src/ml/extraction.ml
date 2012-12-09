open String;;

let extract (args : string) (m: string) (t: string) =
  let extr = open_out "tmp_extr.v" in
  Printf.fprintf extr "Require %s.\nExtraction Language Scheme.\nRecursive Extraction %s.%s.\n"
    m m t;
  flush extr;
  (* Run the extraction, then chop off the first 4 lines because
     the parser can't handle them *)
(*  let status = Unix.system "coqc -R ../ CoqCompile -R ../../coq-ext-lib/theories/ ExtLib tmp_extr.v | tail -n +4 > tmp_extr.scheme" in *)
  let status = Unix.system ("coqc" ^ args ^ " tmp_extr.v | tail -n +4 > tmp_extr.scheme") in 
  match status with
    | Unix.WEXITED 0 -> 
      let scheme_file = open_in "tmp_extr.scheme" in
      let length = in_channel_length scheme_file in
      let extracted_source = create length in
      really_input scheme_file extracted_source 0 length;
      extracted_source;
    | _ -> failwith "Extraction failed."

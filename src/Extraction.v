Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Extraction Blacklist String List.

(* Normally I prefer to do Recursive Extraction Library, but there are
   so many files in Extlib that have axioms (it seems) even though
   we're not using them - these will automatically trigger "failwiths"
   when the extracted code opens the module in question, even though
   no axioms in that module are used. 

   Instead we'll use Extraction to one monolithic file. *)

(* This still has parameters, but obviously at some point we want to switch to this *)
Require Import CoqCompile.Compile.
Definition topcompile := Compile.Compile.topCompileFromStr 8.
Extraction "Extraction/Compile.ml" topcompile.

Require Import CoqCompile.CpsKSemantics.
Definition topeval := evalstr.
Extraction "Extraction/CpsKSemantics.ml" topeval.

(* Just for testing purposes. *)
(*
Require Parse.
Extraction "extraction/Compile.ml" Parse.Parse.parse_topdecls.
*)

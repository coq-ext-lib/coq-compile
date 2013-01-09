Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import String.
Extraction Blacklist String List.
Require Import CoqIO.IO_ml.



(* We'll use Extraction to one monolithic file. *)
Require Import CoqCompile.CompileDriver.
Time Extraction "CoqCompile.ml" compile_string opt0 opt1 opt2.

Require Import CoqCompile.CpsKSemantics.
Definition topeval := evalstr.
Time Extraction "CoqCpsKSemantics.ml" topeval val2str.

(* Just for testing purposes. *)
(*
Require Parse.
Extraction "extraction/Compile.ml" Parse.Parse.parse_topdecls.
*)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import String.
Extraction Blacklist String List.

(* Instead we'll use Extraction to one monolithic file. *)

Require Import CoqCompile.Compile.

Definition topcompile :=
  Compile.Compile.topCompileFromStr 8.
Time Extraction "CoqCompile.ml" topcompile.

Require Import CoqCompile.CpsKSemantics.
Definition topeval := evalstr.
Time Extraction "CoqCpsKSemantics.ml" topeval val2str.

(* Just for testing purposes. *)
(*
Require Parse.
Extraction "extraction/Compile.ml" Parse.Parse.parse_topdecls.
*)

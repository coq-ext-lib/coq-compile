Require Import String.
Require Import ExtLib.Data.Strings.
Require Import CoqCompile.Parse.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsKConvert.
Require Import CoqCompile.CpsCommon.
Require Import CoqCompile.Cps.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.CpsKExamples.
Require Import CoqCompile.CloConvK.
Require Import CoqCompile.CpsK2Low.
Require Import CoqCompile.Low.

(*
Extraction Language Scheme.
Recursive Extraction fact.
*)

Definition lambda2low (e:option Lambda.exp) : string.
refine (
  match e with
    | Some e =>
      let cps_e := CpsKConvert.CPS_io e in
      match CPSK.exp_sane (m' := sum string) cps_e with
        | inl err => "CpsConv: " ++ err ++ (String Char.chr_newline (CPSK.exp2string cps_e))
        | inr _ =>
          match ClosureConvert.cloconv_exp cps_e with
            | inl ex => "CloConv: " ++ ex ++ (String Char.chr_newline (CPSK.exp2string cps_e))
            | inr (ds, e) => (* CPSK.exp2string e *)
              match @cpsk2low (sum string) _ _ ds e with
                | inl ex => "Lower: " ++ ex ++ (String Char.chr_newline (CPSK.exp2string cps_e)) (* (String Char.chr_newline (CPSK.exp2string (CPSK.Letrec_e ds e))) *)
                | inr prog => string_of_program prog
              end
          end
      end
    | None => "Parsing failed"%string
  end%string
).
Defined.


Eval compute in lambda2low (Some plus_lam).
Eval compute in lambda2low (Some mult_lam).
Eval compute in lambda2low (Some fact_lam).

Definition identity : string := "(define ident33 (lambda (x) x))"%string.
Definition identity_e := Parse.parse_topdecls identity.
Eval vm_compute in lambda2low identity_e.


Require Import String.
Require Import ExtLib.Data.Strings.
Require Import CoqCompile.Parse.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsKConvert.
Require Import CoqCompile.CpsCommon.
Require Import CoqCompile.Cps.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.CloConvK.
Require Import CoqCompile.CpsK2Low.
Require Import CoqCompile.Low.

Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => n * fact n'
  end.

Extraction Language Scheme.

Recursive Extraction fact.

Definition plus_e := Parse.parse_topdecls
"(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p) `(S ,(@ plus p m))))))".

Definition mult_e := Parse.parse_topdecls
"(define mult (lambdas (n m)
  (match n
     ((O) `(O))
     ((S p) (@ plus m (@ mult p m))))))".

Definition fact_e := Parse.parse_topdecls 
"(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p) `(S ,(@ plus p m))))))
  
(define mult (lambdas (n m)
  (match n
     ((O) `(O))
     ((S p) (@ plus m (@ mult p m))))))
  
(define fact (lambda (n)
  (match n
     ((O) `(S ,`(O)))
     ((S n~) (@ mult n (fact n~))))))".

Definition lambda2low (e:option Lambda.exp) : string.
refine (
  match e with
    | Some e =>
      let cps_e := CpsKConvert.CPS_io e in
      match CPSK.exp_sane (m' := sum string) cps_e with
        | inl err => "CpsConv: " ++ err++ (String Char.chr_newline (CPSK.exp2string cps_e))
        | inr _ =>
          match ClosureConvert.cloconv_exp cps_e with
            | inl ex => "CloConv: " ++ ex ++ (String Char.chr_newline (CPSK.exp2string cps_e))
            | inr (ds, e) => (* CPSK.exp2string e *)
              match cpsk2low ds e with
                | inl ex => "Lower: " ++ ex ++ (String Char.chr_newline (CPSK.exp2string e))
                | inr prog => string_of_program prog
              end
          end
      end
    | None => "Parsing failed"%string
  end%string
).
Defined.

Eval compute in lambda2low plus_e.
Eval compute in lambda2low mult_e.
Eval compute in lambda2low fact_e.
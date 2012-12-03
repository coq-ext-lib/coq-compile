Require CoqCompile.Lambda.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.CpsKConvert.
Require Import CoqCompile.Parse.

Set Implicit Arguments.
Set Strict Implicit.

Definition e1_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e1.

Definition e1_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e1_lam.

Definition e2_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e2.

Definition e2_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e2_lam.

Definition e3_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e3.

Definition e3_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e3_lam.

Definition e4_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e4.

Definition e4_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e4_lam.

Definition e5_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e5.

Definition e5_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e5_lam.

Definition e6_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e6.

Definition e6_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e6_lam.

Definition e7_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e7.

Definition e7_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e7_lam.

Definition e8_lam := 
  Eval vm_compute in Lambda.LambdaNotation.gen Lambda.LambdaNotation.e8.

Definition e8_cpsk : CPSK.exp :=
  Eval vm_compute in CPS_pure e8_lam.



Definition plus_lam :=
  Eval vm_compute in 
    Parse.parse_topdecls
"(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p) `(S ,(@ plus p m))))))".

Definition plus_cpsk : CPSK.exp :=
  Eval vm_compute in
    match plus_lam as plus_e return match plus_e with
                                      | inl _ => unit
                                      | inr x => CPSK.exp
                                    end with
      | inl _ => tt
      | inr e => CPS_pure e 
    end.

Definition mult_lam := 
  Eval vm_compute in Parse.parse_topdecls
"(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p) `(S ,(@ plus p m))))))

(define mult (lambdas (n m)
  (match n
     ((O) `(O))
     ((S p) (@ plus m (@ mult p m))))))".

Definition mult_cpsk : CPSK.exp :=
  Eval vm_compute in
  match mult_lam as plus_e return match plus_e with
                                  | inl _ => unit
                                  | inr x => CPSK.exp
                                end with
    | inl _ => tt
    | inr e => CPS_pure e 
  end.


Definition fact_lam := 
  Eval vm_compute in Parse.parse_topdecls 
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

Definition fact_cpsk : CPSK.exp :=
  Eval vm_compute in
  match fact_lam as plus_e return match plus_e with
                                  | inl _ => unit
                                  | inr x => CPSK.exp
                                end with
    | inl _ => tt
    | inr e => CPS_pure e 
  end.
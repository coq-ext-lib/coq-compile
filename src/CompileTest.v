Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Programming.Show.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.Cps CoqCompile.CpsK.
Require Import CoqCompile.LLVM.
Require Import CoqCompile.CodeGen CoqCompile.CloConvK.
Require Import CoqCompile.ExtractTypes.
Require Import CoqCompile.Parse.
Require Import CoqCompile.TraceMonad.
Require Import CoqCompile.Compile.

Set Implicit Arguments.
Set Strict Implicit.

Module CompileTest.
  Import Lambda.
  Import LambdaNotation.

  Definition identity : string := "(define ident (lambda (x) ident))"%string.

  Definition e_ident : Lambda.exp :=
    Eval compute in 
      match Parse.parse_topdecls identity with
        | inl _ => Lambda.Var_e (Env.wrapVar ""%string)
        | inr o => o
      end.

  Definition fact :=
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
       ((S n~) (@ mult n (fact n~))))))"%string.

  Definition e_fact : Lambda.exp :=
    Eval vm_compute in 
      match Parse.parse_topdecls fact with
        | inl _ => Lambda.Var_e (Env.wrapVar ""%string)
        | inr o => o
      end.

  Eval vm_compute in
    Compile.stringToCPS fact.

  Eval vm_compute in
    Compile.stringToClos fact.

  Eval vm_compute in
    Compile.stringToLow fact.

  (** TODO: This is stack overflowing **)
  Eval vm_compute in
    match Compile.runM (Compile.topCompile 8 Compile.Opt.O0 false e_fact) with
      | (inl err, t) => (err, t)
      | (inr mod', t) => (to_string mod', t)
    end.

End CompileTest.

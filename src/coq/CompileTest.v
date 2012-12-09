Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Programming.Show.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsK CoqCompile.CpsKExamples.
Require Import CoqCompile.LLVM.
Require Import CoqCompile.Parse.
Require Import CoqCompile.TraceMonad.
Require Import CoqCompile.Compile.

Set Implicit Arguments.
Set Strict Implicit.

Module CompileTest.
  Definition identity : string := "(define ident (lambda (x) ident))"%string.

  Definition e_ident : Lambda.exp :=
    Eval compute in 
      match Parse.parse_topdecls identity with
        | inl _ => Lambda.Var_e (Env.wrapVar ""%string)
        | inr o => o
      end.

  Definition hello_world := "
(define __ (lambda (_) __))

(define ret (lambdas (monad x)
  (match monad
     ((Build_Monad ret0 bind0) (@ ret0 __ x)))))

(define bind (lambdas (monad x x0)
  (match monad
     ((Build_Monad ret0 bind0) (@ bind0 __ x __ x0)))))

(define monoid_plus (lambda (m)
  (match m
     ((Build_Monoid monoid_plus0 monoid_unit0) monoid_plus0))))

(define monoid_unit (lambda (m)
  (match m
     ((Build_Monoid monoid_plus0 monoid_unit0) monoid_unit0))))

(define inject (lambda (injection) injection))

(define chr_newline `(Ascii ,`(False) ,`(True) ,`(False) ,`(True) ,`(False)
  ,`(False) ,`(False) ,`(False)))

(define show_mon (lambda (showScheme)
  (match showScheme
     ((Build_ShowScheme show_mon0 show_inj0) show_mon0))))

(define show_inj (lambda (showScheme)
  (match showScheme
     ((Build_ShowScheme show_mon0 show_inj0) show_inj0))))

(define runShow (lambdas (m m0) (@ m0 __ (show_inj m) (show_mon m))))

(define show (lambdas (show0 x x0 x1) (@ show0 x __ x0 x1)))

(define empty (lambdas (x m) (monoid_unit m)))

(define cat (lambdas (a b i m) (@ monoid_plus m (@ a __ i m) (@ b __ i m))))

(define injection_ascii_showM (lambdas (v i x) (i v)))

(define show_exact (lambdas (s x x0)
  (match s
     ((EmptyString) (@ empty x x0))
     ((String a s~)
       (@ cat (@ inject (lambdas (x1 _) (injection_ascii_showM x1)) a)
         (lambda (_) (show_exact s~)) x x0)))))
  
(define _inject_char (lambdas (x x0 x1)
  (@ inject (lambdas (x2 _) (injection_ascii_showM x2)) x __ x0 x1)))

(define ascii_Show (lambdas (a x x0)
  (@ cat (lambda (_)
    (@ cat (lambda (_)
      (_inject_char `(Ascii ,`(True) ,`(True) ,`(True) ,`(False) ,`(False)
        ,`(True) ,`(False) ,`(False)))) (lambda (_) (_inject_char a))))
    (lambda (_)
    (_inject_char `(Ascii ,`(True) ,`(True) ,`(True) ,`(False) ,`(False)
      ,`(True) ,`(False) ,`(False)))) x x0)))

(define iO_bind io_bind)

(define iO_ret io_ret)

(define iO_printChar io_printChar)

(define monad_IO `(Build_Monad ,(lambda (_) iO_ret) ,(lambdas (_ x _)
  (iO_bind x))))

(define showScheme_IO `(Build_ShowScheme ,`(Build_Monoid ,(lambdas (x y)
  (@ bind monad_IO x (lambda (x0) y))) ,(@ ret monad_IO `(Tt)))
  ,iO_printChar))

(define main
  (@ runShow showScheme_IO (lambda (_)
    (@ cat (lambda (_)
      (show_exact `(String ,`(Ascii ,`(False) ,`(False) ,`(False) ,`(True)
        ,`(False) ,`(False) ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(True)
        ,`(False) ,`(False) ,`(False) ,`(False) ,`(True) ,`(False) ,`(False))
        ,`(EmptyString))))) (lambda (_)
      (@ show (lambdas (x _) (ascii_Show x)) chr_newline))))))"%string.

  Definition e_hello : Lambda.exp :=
    Eval vm_compute in 
      match Parse.parse_topdecls hello_world with
        | inl _ => Lambda.Var_e (Env.wrapVar ""%string)
        | inr o => o
      end.

(*
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

  Definition broke :=
   "(define __ (lambda (_) __))

(define ret (lambdas (monad x)
  (match monad
     ((Build_Monad ret0 bind0) (@ ret0 __ x)))))

(define bind (lambdas (monad x x0)
  (match monad
     ((Build_Monad ret0 bind0) (@ bind0 __ x __ x0)))))

(define monoid_plus (lambda (m)
  (match m
     ((Build_Monoid monoid_plus0 monoid_unit0) monoid_plus0))))

(define monoid_unit (lambda (m)
  (match m
     ((Build_Monoid monoid_plus0 monoid_unit0) monoid_unit0))))

(define inject (lambda (injection) injection))

(define chr_newline `(Ascii ,`(False) ,`(True) ,`(False) ,`(True) ,`(False)
  ,`(False) ,`(False) ,`(False)))

(define show_mon (lambda (showScheme)
  (match showScheme
     ((Build_ShowScheme show_mon0 show_inj0) show_mon0))))

(define show_inj (lambda (showScheme)
  (match showScheme
     ((Build_ShowScheme show_mon0 show_inj0) show_inj0))))

(define runShow (lambdas (m m0) (@ m0 __ (show_inj m) (show_mon m))))

(define show (lambdas (show0 x x0 x1) (@ show0 x __ x0 x1)))

(define empty (lambdas (x m) (monoid_unit m)))

(define cat (lambdas (a b i m) (@ monoid_plus m (@ a __ i m) (@ b __ i m))))

(define injection_ascii_showM (lambdas (v i x) (i v)))

(define show_exact (lambdas (s x x0)
  (match s
     ((EmptyString) (@ empty x x0))
     ((String a s~)
       (@ cat (@ inject (lambdas (x1 _) (injection_ascii_showM x1)) a)
         (lambda (_) (show_exact s~)) x x0)))))
  
(define _inject_char (lambdas (x x0 x1)
  (@ inject (lambdas (x2 _) (injection_ascii_showM x2)) x __ x0 x1)))

(define ascii_Show (lambdas (a x x0)
  (@ cat (lambda (_)
    (@ cat (lambda (_)
      (_inject_char `(Ascii ,`(True) ,`(True) ,`(True) ,`(False) ,`(False)
        ,`(True) ,`(False) ,`(False)))) (lambda (_) (_inject_char a))))
    (lambda (_)
    (_inject_char `(Ascii ,`(True) ,`(True) ,`(True) ,`(False) ,`(False)
      ,`(True) ,`(False) ,`(False)))) x x0)))

(define iO_bind io_bind)

(define iO_ret io_ret)

(define iO_printChar io_printChar)

(define monad_IO `(Build_Monad ,(lambda (_) iO_ret) ,(lambdas (_ x _)
  (iO_bind x))))

(define showScheme_IO `(Build_ShowScheme ,`(Build_Monoid ,(lambdas (x y)
  (@ bind monad_IO x (lambda (x0) y))) ,(@ ret monad_IO `(Tt)))
  ,iO_printChar))

(define main
  (@ runShow showScheme_IO (lambda (_)
    (@ cat (lambda (_)
      (show_exact `(String ,`(Ascii ,`(False) ,`(False) ,`(False) ,`(True)
        ,`(False) ,`(False) ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(True)
        ,`(False) ,`(True) ,`(False) ,`(False) ,`(True) ,`(True) ,`(False))
        ,`(String ,`(Ascii ,`(False) ,`(False) ,`(True) ,`(True) ,`(False)
        ,`(True) ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(False) ,`(False)
        ,`(True) ,`(True) ,`(False) ,`(True) ,`(True) ,`(False)) ,`(String
        ,`(Ascii ,`(True) ,`(True) ,`(True) ,`(True) ,`(False) ,`(True)
        ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(False) ,`(False) ,`(False)
        ,`(False) ,`(False) ,`(True) ,`(False) ,`(False)) ,`(String ,`(Ascii
        ,`(True) ,`(True) ,`(True) ,`(False) ,`(True) ,`(True) ,`(True)
        ,`(False)) ,`(String ,`(Ascii ,`(True) ,`(True) ,`(True) ,`(True)
        ,`(False) ,`(True) ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(False)
        ,`(True) ,`(False) ,`(False) ,`(True) ,`(True) ,`(True) ,`(False))
        ,`(String ,`(Ascii ,`(False) ,`(False) ,`(True) ,`(True) ,`(False)
        ,`(True) ,`(True) ,`(False)) ,`(String ,`(Ascii ,`(False) ,`(False)
        ,`(True) ,`(False) ,`(False) ,`(True) ,`(True) ,`(False)) ,`(String
        ,`(Ascii ,`(True) ,`(False) ,`(False) ,`(False) ,`(False) ,`(True)
        ,`(False) ,`(False)) ,`(EmptyString))))))))))))))) (lambda (_)
      (@ show (lambdas (x _) (ascii_Show x)) chr_newline))))))"%string.

  Definition e_broke : Lambda.exp :=
    Eval vm_compute in 
      match Parse.parse_topdecls broke with
        | inl _ => Lambda.Var_e (Env.wrapVar ""%string)
        | inr o => o
      end.
*)

  Definition c_hello : CPSK.exp :=
    Eval vm_compute in 
      CpsKConvert.CPS_io e_hello.

  Require Import ExtLib.Data.Monads.EitherMonad.

  Definition cc_hello : string + (list CPSK.decl * CPSK.exp) :=
    Eval vm_compute in
      CloConvK.ClosureConvert.cloconv_exp c_hello.

  Definition low_hello : string + Low.program :=
    Eval vm_compute in
      match cc_hello as cc_hello return match cc_hello with
                                          | inl _ => unit
                                          | inr _ => string + Low.program
                                        end
        with
        | inl _ => tt
        | inr (ds, main) =>
          CpsK2Low.cpsk2low (sum string) ds main
      end.
(* Stack overflow
  Eval vm_compute in to_string low_hello.
*)

(*
  Eval vm_compute in
    Compile.lamToCPSIO e_hello.

  Eval vm_compute in
    Compile.lamToClosIO e_hello.

  Eval compute in
    Compile.lamToLowIO e_hello.
*)
(*
  (** TODO: This is stack overflowing **)
  Eval vm_compute in
    match Compile.runM (Compile.topCompile 8 Compile.Opt.O0 false e_fact) with
      | (inl err, t) => (err, t)
      | (inr mod', t) => (to_string mod', t)
    end.
*)
End CompileTest.

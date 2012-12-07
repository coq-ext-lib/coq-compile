Require Import String List Bool.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.Analyze.CFA0.
Require Import CoqCompile.CpsKUtil.
Require Import CoqCompile.Analyze.Reachability.
Require Import CoqCompile.Opt.CopyPropCpsK.
Require Import CoqCompile.TraceMonad.

Import CpsK.CPSK.

Module TEST_REACHABLE.
  Require Import CoqCompile.Parse.
  Require Import ExtLib.Programming.Show.
  Require CoqCompile.CpsKConvert.

  Extraction Language Scheme.

  Definition test3 := 
    let x := 3 in
    let y := S x in
    y.

  Recursive Extraction test3.
  Definition test3_s := "(define test3 (let ((x `(S ,`(S ,`(S ,`(O)))))) `(S ,x)))"%string.

  Definition test3_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test3_s.
  
  Definition test3_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test3_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.

  Definition f := fun x => S x.
  Definition g := fun (x y:nat) => y.
  Definition test4 := g (f (f 1)) 1.
  
  Recursive Extraction test4.
  Definition test4_s := 
  "(define f (lambda (x) `(S ,x)))
  
  (define g (lambdas (x y) y))
  
  (define test4 (@ g (f (f `(S ,`(O)))) `(S ,`(O))))"%string.

  Definition test4_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test4_s.
  
  Definition test4_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test4_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.

  Definition test5 := 
    let x := f 1 in
    let y := f x in
    let z := f y in
    let a := f 1 in
    let b := f a in
    f b.
  Recursive Extraction test5.
  Definition test5_s := "(define f (lambda (x) `(S ,x)))

  (define test5 (let ((a (f `(S ,`(O))))) (let ((b (f a))) (f b))))"%string.

  Definition test5_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test5_s.
  
  Definition test5_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test5_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.

  Require Import ExtLib.Data.Monads.StateMonad.
  Import MonadNotation.
  Local Open Scope monad_scope.
  Print MonadState.

  Fixpoint test6 (n:nat) : state nat unit :=
    match n with
      | O => ret tt
      | S n' => gets (fun x => x) ;; test6 n'
    end.
  Recursive Extraction test6.
  Definition test6_s := "(define __ (lambda (_) __))

(define ret (lambdas (monad x)
  (match monad
     ((Build_Monad ret0 bind0) (@ ret0 __ x)))))

(define bind (lambdas (monad x x0)
  (match monad
     ((Build_Monad ret0 bind0) (@ bind0 __ x __ x0)))))

(define get (lambda (monadState)
  (match monadState
     ((Build_MonadState get0 put) get0))))

(define gets (lambdas (m mS f)
  (@ bind m (get mS) (lambda (x) (@ ret m (f x))))))

(define runState (lambda (s) s))

(define monad_state `(Build_Monad ,(lambdas (_ v s) `(Pair ,v ,s))
  ,(lambdas (_ c1 _ c2 s)
  (match (@ runState c1 s)
     ((Pair v s0) (@ runState (c2 v) s0))))))

(define monadState_state `(Build_MonadState ,(lambda (x) `(Pair ,x ,x))
  ,(lambdas (v x) `(Pair ,`(Tt) ,v))))

(define test6 (lambda (n)
  (match n
     ((O) (@ ret monad_state `(Tt)))
     ((S n~)
       (@ bind monad_state
         (@ gets monad_state monadState_state (lambda (x) x)) (lambda (x)
         (test6 n~)))))))"%string.

  Definition test6_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test6_s.
  
  Require Import CoqCompile.Optimize.
  Require CoqCompile.Opt.CseCpsK.
  Require CoqCompile.Opt.DeadCodeCpsK.
  Require CoqCompile.Opt.ReduceCpsK.
  Definition test6_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test6_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => (* CpsKConvert.CPS_pure e *)
          ReduceCpsK.Reduce.reduce (CseCpsK.Cse.cse (DeadCodeCpsK.dce (CpsKConvert.CPS_pure e )))
      end.

  Fixpoint wtf (n acc:nat):=
    match n with
      | O => acc
      | S n' => wtf n' (S acc)
    end.
  Definition test7 := wtf 3 0.
  Recursive Extraction test7.
  Definition test7_s := "
  (define wtf (lambdas (n acc)
  (match n
     ((O) acc)
     ((S n~) (@ wtf n~ `(S ,acc))))))
  
(define test7 (@ wtf `(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))) `(O)))"%string.
  
  Definition test7_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test7_s.
  
  Definition test7_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test7_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e
      end.
    
  Require Import CoqCompile.Lambda.
  Import Lambda.LambdaNotation.

  Definition test8_lam : Lambda.exp :=
    gen(
    def x := S_c (S_c Z_c) in
    def y := S_c Z_c in
    y).

  Definition test8_cpsk : CPSK.exp := CpsKConvert.CPS_pure test8_lam.

  Definition test9_lam : Lambda.exp :=
    gen(
    def x := S_c Z_c in
    def y := S_c Z_c in
    def a := S_c x in
    def z := S_c Z_c in
    a).

  Definition test9_cpsk : CPSK.exp := CpsKConvert.CPS_pure test9_lam.

  Section hiding_notation.
    Import ShowNotation.
    Local Open Scope show_scope.
    Local Open Scope string_scope.

    Global Instance Show_stuff : Show D :=
    { show := fun m => sepBy_f (fun kv => show (fst kv) << " : " << show (snd kv)) Char.chr_newline m }.
  End hiding_notation.


    Definition ident (x: nat) := x.

  Definition call_ident :=
    let x := 0 in
      let y := 1 in
        let z := ident x in
          (y,z).
  Recursive Extraction call_ident. 

  Definition ident_s := 
"(define ident (lambda (x) x))

(define call_ident
  (let ((x `(O))) (let ((y `(S ,`(O)))) (let ((z (ident x))) `(Pair ,y ,z)))))"%string.
  Definition ident_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls ident_s.

  Definition ident_cpsk : CPSK.exp :=
    Eval vm_compute in
      match ident_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => (CpsKConvert.CPS_pure e) 
      end.

  Section monadic.
    Require Import CoqCompile.TraceMonad.
    Require Import ExtLib.Data.Monads.EitherMonad.
    Import MonadNotation.
    Local Open Scope monad_scope.

    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Trace_m : MonadTrace string m}.
    Context {Exc_m : MonadExc string m}.

    Require Import CoqCompile.CloConvK.
    Require Import CoqCompile.Low.
    Require Import CoqCompile.CpsK2Low.
    Definition ident_cc : m (list decl * exp) :=
      CloConvK.ClosureConvert.cloconv_exp ident_cpsk.

    Definition ident_reach : m D :=
      ident_cpsk <- ident_cc ;;
      let ident_cpsk := Letrec_e (fst ident_cpsk) (snd ident_cpsk) in
      dom <- cfa_n m 0 ident_cpsk 10 ;; 
      let dom' := reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10 in
      match dom' with
        | Some dom'' => ret dom''
        | None => raise "reachable: out of fuel"%string
      end.
    
    Definition ident_live : m (alist (var + CPSK.cont) (lset (@eq (var + CPSK.cont)))) :=
      ident_cpsk <- ident_cc ;;
      let ident_cpsk := Letrec_e (fst ident_cpsk) (snd ident_cpsk) in
      reach <- ident_reach ;;
      ret (live_exp reach ident_cpsk Maps.empty).

    Definition ident_low : m Low.program :=
      live <- ident_live ;;
      ident_cc <- ident_cc ;;
      cpsk2low_dupdate _ live (fst ident_cc) (snd ident_cc).

    Definition test8_cc : m (list decl * exp) :=
      CloConvK.ClosureConvert.cloconv_exp test8_cpsk.

    Definition test8_low : m Low.program.
    refine(
      blah <- test8_cc ;;
      live <- construct_live_map _ test8_cpsk 12 ;;
      cc <- test8_cc ;;
      cpsk2low_h _ live (fst cc) (snd cc)).
    Defined.

    Definition test8_low2 : m Low.program.
    refine(
      blah <- test8_cc ;;
      live <- construct_live_map _ test8_cpsk 12 ;;
      cc <- test8_cc ;;
      cpsk2low_h _ None (fst cc) (snd cc)).
    Defined.

    Definition test9_cc : m (list decl * exp) :=
      CloConvK.ClosureConvert.cloconv_exp (CopyProp.copyprop test9_cpsk).

    Definition test9_low : m Low.program.
    refine(
      blah <- test9_cc ;;
      let blah := CopyProp.copyprop (Letrec_e (fst blah) (snd blah)) in
      live <- construct_live_map _ blah 12 ;;
      cc <- test9_cc ;;
      cpsk2low_h _ live (fst cc) (snd cc)).
    Defined.

    Definition test9_reach : m D :=
      ident_cpsk <- test9_cc ;;
      let ident_cpsk := Letrec_e (fst ident_cpsk) (snd ident_cpsk) in
      let ident_cpsk := CopyProp.copyprop ident_cpsk in
      dom <- cfa_n m 0 ident_cpsk 10 ;; 
      let dom' := reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10 in
      match dom' with
        | Some dom'' => ret dom''
        | None => raise "reachable: out of fuel"%string
      end.
    
    Definition test9_live : m (alist (var + CPSK.cont) (lset (@eq (var + CPSK.cont)))) :=
      ident_cpsk <- test9_cc ;;
      let ident_cpsk := Letrec_e (fst ident_cpsk) (snd ident_cpsk) in
      reach <- test9_reach ;;
      ret (live_exp reach ident_cpsk Maps.empty).

  End monadic.

  Definition blah : string + D :=
    match traceTraceT (test9_reach _) with
      | inl err => inl err
      | inr (dom, str) => inr (live_exp dom (CopyProp.copyprop test9_cpsk) Maps.empty)
    end.

  Eval vm_compute in to_string blah.

  (*
  Eval vm_compute in 
    match traceTraceT (test9_reach _) with
      | inl err => err
      | inr dom => to_string (live_set dom (CopyProp.copyprop test9_cpsk))
    end.
    *)

  Eval vm_compute in 
    match traceTraceT (test9_cc _) with
      | inl err => err
      | inr dom => to_string dom
    end.

  Eval vm_compute in 
    match traceTraceT (test9_live _) with
      | inl err => err
      | inr dom => ("wtf" ++ to_string dom)%string
    end.

  Import ShowNotation.
  Local Open Scope show_scope.

  Global Instance Show_special : Show (Low.program * list string) :=
  { show x := let '(a,b) := x in
    Char.chr_newline << show a <<
    Char.chr_newline << Char.chr_newline <<
    sepBy_f (fun x => show_exact x) Char.chr_newline b <<
    Char.chr_newline }.

  Require  Import ExtLib.Data.Monads.EitherMonad.
  Require Import ExtLib.Data.Monads.IdentityMonad.

  About test9_low.
  Eval vm_compute in 
    match unIdent (traceTraceT (unEitherT (test9_low _))) with
      | (inl err, tr) => err
      | (inr dom, tr) => to_string dom
    end.
  
  Eval vm_compute in 
    match (traceTraceT (test8_low _)) with
      | inl err => err
      | inr dom => to_string dom
    end.

  Eval vm_compute in 
    match (traceTraceT (test8_low2 _)) with
      | inl err => err
      | inr dom => to_string dom
    end.

  Require Import ExtLib.Data.Monads.IdentityMonad.
  Eval vm_compute in to_string (CloConvK.ClosureConvert.cloconv_exp ident_cpsk).
  Eval vm_compute in 
    match (traceTraceT (ident_low _)) with
      | inl err => err
      | inr dom => to_string dom
    end.
  Eval vm_compute in 
    match (traceTraceT (ident_reach _)) with
      | inl err => err
      | inr dom => to_string dom
    end.
  Eval vm_compute in 
    match (traceTraceT (ident_live _)) with
      | inl err => err
      | inr dom => to_string dom
    end.

  
(*
  Definition test3_reach :=
    let '(r, tr) := cfa_n 0 test3_cpsk 10 in
    match r with
      | inl err => inl err
      | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10)
    end.

  Eval vm_compute in to_string test3_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test3_cpsk 10) in to_string r.
  Time Eval vm_compute in to_string (test3_reach).

  Eval vm_compute in
    to_string
    match test3_reach with
      | inl err => inl err
      | inr reach => match reach with
                       | Some reach => inr (live_exp reach test3_cpsk Maps.empty)
                       | None => inl "reachability analysis failed"%string
                     end
    end.

  Definition test4_reach :=
    let '(r, tr) := cfa_n 0 test4_cpsk 10 in
    match r with
      | inl err => inl err
      | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10)
    end.

  Eval vm_compute in to_string test4_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test4_cpsk 10) in to_string r.
  Time Eval vm_compute in to_string (test4_reach).

  Definition test5_reach :=
    let '(r, tr) := cfa_n 0 test5_cpsk 10 in
    match r with
      | inl err => inl err
      | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10)
    end.

  Eval vm_compute in to_string test5_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test5_cpsk 10) in to_string r.
  Time Eval vm_compute in to_string (test5_reach).

  Definition test6_reach :=
    let '(r, tr) := cfa_n 0 test6_cpsk 10 in
      match r with
        | inl err => inl err
        | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10)
      end.
  
  Eval vm_compute in to_string test6_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test6_cpsk 10) in to_string r.
  Time Eval vm_compute in to_string (test6_reach).

  Definition test7_reach :=
    let '(r, tr) := cfa_n 0 test7_cpsk 20 in
      match r with
        | inl err => inl err
        | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 20)
      end.
  
  Eval vm_compute in to_string test7_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test7_cpsk 20) in to_string r.
  Time Eval vm_compute in to_string (test7_reach).    

  Eval vm_compute in
    to_string
    match test7_reach with
      | inl err => inl err
      | inr reach => match reach with
                       | Some reach => inr (live_exp reach test7_cpsk Maps.empty)
                       | None => inl "reachability analysis failed"%string
                     end
    end.
*)

End TEST_REACHABLE.
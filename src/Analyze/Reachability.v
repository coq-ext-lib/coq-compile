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

Import CpsK.CPSK.

Section REACHABLE.
    
  Definition useful_ptv (v:PtValue unit) : lset (@eq (var + cont)) :=
    match v with
      | Ctor c => Sets.empty
      | Int i => Sets.empty
      | Ptr l => Sets.singleton (inl l)
      | Clo c pp ks xs e =>
        match pp with
          | inl v => free_vars_decl true (Fn_d v ks xs e)
          | inr k => free_vars_cont k xs e
        end
    end.

  Definition useful (vs:lset (@eq (PtValue unit))) : lset (@eq (var + cont)) :=
    fold (fun v acc => Sets.union acc (useful_ptv v)) Sets.empty vs.

  Definition D : Type := alist (var + cont) (lset (@eq (var + cont))).

  Definition reachable_1 (env:alist (var + cont) (Value unit)) (dom:D) : D.
  refine (
    fold (fun kv acc => 
      let '(k, v) := kv in 
      let res := match v with
                   | Any => keys _ _ env
                   | Values vs => _
                 end in
      Maps.add k res acc) dom env).
  refine (match Maps.lookup k acc with
            | Some old_set => Sets.union old_set (useful vs)
            | None => useful vs
          end).
  Defined.
  
  Definition reachable_2 (heap:alist var (list (Value unit))) (dom : D) : D :=
    fold (fun kv acc =>
      let '(k,v) := kv in
      let res := fold (fun v' acc' =>
        match v' with
          | inl v' =>
            match Maps.lookup v' heap with
              | None => acc'
              | Some vs => List.fold_left (fun acc x =>
                match x with
                  | Any => map (fun x => inl x) (keys _ (s := lset (@eq var)) _ heap)
                  | Values vs => Sets.union (useful vs) acc
                end ) vs acc'
            end
          | inr _ => acc'
        end) v v in
      Maps.add k res acc) dom dom.

  Require Import BinNums.
  Require Import ExtLib.Data.Monads.FuelMonad.
  Require Import ExtLib.Data.Monads.IdentityMonad.
  
  Definition least_fixpoint {A} (leq : A -> A -> bool) (f : A -> A) (init : A) (fuel : N) : option A :=
    unIdent (runGFixT (mfix (fun recur x =>
      let x' := f x in
      if leq x' x then ret x' else recur x') init) fuel).

  Definition dom_eq (d1 d2 : D) : bool :=
    let f := fun s1 s2 => (Sets.subset s1 s2) && Sets.subset s2 s1 in
    submap_with _ f d1 d2 &&
    submap_with _ f d2 d1.

  Definition reachable (env:alist (var + cont) (Value unit)) (heap:alist var (list (Value unit))) (fuel : N) : option D :=
    least_fixpoint dom_eq (reachable_2 heap) (reachable_1 env Maps.empty) fuel.
  
End REACHABLE.  

Section LIVENESS.
  
  Variable reach : alist (var + cont) (lset (@eq (var + cont))).

  (* let x = <1, 2>
          .
          .
          .
     let y = <3, 4>
          .
          .
          .
     in k z

   *)

  (* Do we need this??? *)
  Fixpoint escape_cont_exp (e:exp) (acc:lset (@eq (var + cont))) : (lset (@eq (var + cont))) :=
    match e with
      | App_e o ks os => acc
      | Let_e d e' => escape_cont_exp e' (Sets.union (escape_cont_decl d acc) acc)
      | Letrec_e ds e' =>
        escape_cont_exp e' (List.fold_left (fun acc' x => Sets.union (escape_cont_decl x acc) acc') ds acc)
      | Switch_e o arms def =>
        let arms_escape := List.fold_left (fun acc' x => 
          let '(p, e) := x in Sets.union (escape_cont_exp e acc) acc') arms acc in
        match def with
          | Some e => Sets.union arms_escape (escape_cont_exp e acc)
          | None => arms_escape
        end
      | Halt_e o1 o2 => acc 
      | AppK_e k os => List.fold_left (fun acc' x => match x with
                                                      | Var_o x => Sets.add (inl x) acc'
                                                      | _ => acc'
                                                    end) os acc
      | LetK_e kves e' =>
        List.fold_left (fun acc' x => let '(k,x,e) := x in
          Sets.union (escape_cont_exp e acc) acc') kves acc
    end
  with escape_cont_decl (d:decl) (acc:lset (@eq (var + cont))) : (lset (@eq (var + cont))) :=
    match d with
      | Op_d x os => acc
      | Prim_d x p os => acc 
      | Fn_d x ks xs e => escape_cont_exp e acc
      | Bind_d x w m os => acc
    end.

  Definition live_set (e:exp) : (lset (@eq (var + cont))) :=
    (* let escape := Sets.union (free_vars_exp e) (escape_cont_exp e Sets.empty) in *)
    let escape := free_vars_exp e in
    fold (fun x acc => match Maps.lookup x reach with
                         | Some s => Sets.union s acc
                         | None => acc
                       end) Sets.empty escape.

  Definition var_of_decl (d:decl) : var :=
    match d with
      | Op_d x _ => x
      | Prim_d x _ _ => x
      | Fn_d x _ _ _ => x
      | Bind_d x _ _ _ => x
    end.

  Fixpoint live_exp (e:exp) (dom:alist (var + cont) (lset (@eq (var + cont)))) :
    alist (var + cont) (lset (@eq (var + cont))) :=
    match e with
      | App_e o ks os => dom
      | Let_e d e' =>
        let live_stuff := live_set e' in
        let x := var_of_decl d in
        let live_stuff := match Maps.lookup (inl x) dom with
                            | Some old_set => Sets.union old_set live_stuff
                            | None => live_stuff
                          end in
        let dom' := live_decl d (Maps.add (inl x) live_stuff dom) in
        live_exp e' dom'
      | Letrec_e ds e' =>
        List.fold_left (fun acc d =>
          let live_stuff := live_set e' in
          let x := var_of_decl d in
          let live_stuff := match Maps.lookup (inl x) acc with
                              | Some old_set => Sets.union old_set live_stuff
                              | None => live_stuff
                            end in
          let dom' := Maps.add (inl x) live_stuff acc in
          let dom' := live_decl d dom' in
          live_exp e' dom') ds dom
      | Switch_e o arms def =>
        let dom' := List.fold_left (fun acc x => let '(p, e') := x in 
          Maps.combine (fun k v1 v2 => Sets.union v1 v2) (live_exp e' acc) acc) arms dom in
        match def with
          | Some e' => Maps.combine (fun k v1 v2 => Sets.union v1 v2) (live_exp e' dom') dom'
          | None => dom'
        end
      | Halt_e o1 o2 => dom
      | AppK_e k os => dom
      | LetK_e kxse e' =>
        let dom' := List.fold_left (fun acc x => let '(k, xs, e') := x in
          live_exp e' acc) kxse dom in
        live_exp e' dom'
    end
  with live_decl (d:decl) (dom:alist (var + cont) (lset (@eq (var + cont)))) :
    alist (var + cont) (lset (@eq (var + cont))) :=
    match d with
      | Op_d x os => dom
      | Prim_d x p os => dom
      | Fn_d x ks xs e => live_exp e dom
      | Bind_d x w m os => dom
    end.

End LIVENESS.

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
  Definition test7 := wtf 5 0.
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
  
  Definition sanitize {A B} {_ : RelDec (@eq B)} (env:alist (unit * B) A) : (alist B A) :=
    fold (fun kv acc => 
      let '(k, v) := kv in
      let '(_, k) := k in
      Maps.add k v acc) Maps.empty env.
  
  Section hiding_notation.
    Import ShowNotation.
    Local Open Scope show_scope.
    Local Open Scope string_scope.

    Global Instance Show_stuff : Show D :=
    { show := fun m => sepBy_f (fun kv => show (fst kv) << " : " << show (snd kv)) Char.chr_newline m }.
  End hiding_notation.

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

End TEST_REACHABLE.
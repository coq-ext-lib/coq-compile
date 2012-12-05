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

(*
Module TEST_REACHABLE.
  Require Import CoqCompile.Parse.
  Require Import ExtLib.Programming.Show.
  Require CoqCompile.CpsKConvert.

  Definition test2_s :=
  "(define g (lambdas (x y) x))
  
  (define h (lambda (x) `(S ,x)))
  
  (define test2 (@ g (h (h `(S ,`(O)))) `(S ,`(O))))"%string.

  Definition test2_lam :=
    Eval vm_compute in 
      Parse.parse_topdecls test2_s.
  
  Definition test2_cpsk : CPSK.exp :=
    Eval vm_compute in
      match test2_lam as plus_e return match plus_e with
                                         | inl _ => unit
                                         | inr x => CPSK.exp
                                       end with
        | inl _ => tt
        | inr e => CpsKConvert.CPS_pure e 
      end.

Definition test3 := 
  let x := 3 in
  let y := S x in
  y.

Extraction Language Scheme.
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

  Definition test3_blah :=
    let '(r, tr) := cfa_n 0 test3_cpsk 10 in
    match r with
      | inl err => inl err
      | inr dom => inr (reachable (sanitize (env _ dom)) (sanitize (heap _ dom)) 10)
    end.

  Definition test3_blah2 : option D :=
    let '(r, tr) := cfa_n 0 test3_cpsk 10 in
    match r with
      | inl err => None
      | inr dom => Some (reachable_1 (sanitize (env _ dom)) Maps.empty)
    end.
  (*
  Definition test3_blah3 : option D :=
    let '(r, tr) := cfa_n 0 test3_cpsk 10 in
    match r with
      | inl err => None
      | inr dom => Some (reachable_2 (reachable_1 (sanitize (env _ dom)) Maps.empty))
    end.
  Eval vm_compute in to_string test3_blah2.
  Eval vm_compute in match test3_blah2 with
                       | Some d => dom_eq Maps.empty d
                       | None => false
                     end.
                     *)

  Eval vm_compute in to_string test3_cpsk.
  Time Eval vm_compute in
    let '(r,tr) := (cfa_n 0 test3_cpsk 10) in to_string r.
  Time Eval vm_compute in to_string (test3_blah).


End TEST_REACHABLE.
*)
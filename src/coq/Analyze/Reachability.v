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

Section monadic.
  Require Import CoqCompile.TraceMonad.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadTrace_m : MonadTrace string m}.
  Context {MonadExc_m : MonadExc string m}.

  Definition sanitize {A B} {_ : RelDec (@eq B)} (env:alist (unit * B) A) : (alist B A) :=
    fold (fun kv acc => 
      let '(k, v) := kv in
      let '(_, k) := k in
      Maps.add k v acc) Maps.empty env.

  Require Import CoqCompile.Opt.CopyPropCpsK.

  Definition construct_live_map (e:exp) (fuel:N) : m (option (alist (var + cont) (lset (@eq (var + cont))))) :=
    catch (
      let e := CopyProp.copyprop e in
      domain <- cfa_n _ 0 e fuel ;;
      let sanitized := sanitize (env _ domain) in
      let sanitized_heap := sanitize (heap _ domain) in
      match reachable sanitized sanitized_heap fuel with
        | None => raise "reachable ran out of fuel"%string
        | Some dom' =>
        let live := live_exp dom' e Maps.empty in
          ret (Some live)
      end
    ) (fun err =>
      mlog ("construct_live_map failed: " ++ err)%string ;;
      ret None
    ).
End monadic.


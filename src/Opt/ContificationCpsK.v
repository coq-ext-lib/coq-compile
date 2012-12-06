Require Import String List.
Require Import CoqCompile.CpsK.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Data.Map.FMapAList.

Set Implicit Arguments.
Set Strict Implicit.

Section map_monoid.
  Variable M : Type -> Type.
  Variable K : Type.
  Variable E : Type.
  Variable Monoid_e : Monoid E.
  Context {DMap_M : DMap K M}.
  Context {Foldable_M : Foldable (M E) (K * E)}.   

  Definition Monoid_map : Monoid (M E) :=
  {| monoid_unit := Maps.empty
   ; monoid_plus := Maps.combine (K := K) (fun _ => monoid_plus Monoid_e)
  |}.
End map_monoid.


Module Contify.
  
  Import CpsK.CPSK.


  (** A function [f] can be made into a continuation [k] if all execution
   ** paths in [f] return to the same continuation.
   **
   ** Further: The function must be in the scope of the continuation (can I move it?).
   ** In particular, this means that I can not contify a function inside a function
   ** if I know that it refers to the outer continuation.
   ** - My analysis should never say that I can do this because we always do return
   **   to a passed-in continuation
   **)

  Section monadic.
    Let monoid : Monoid (alist var (lset (@eq (list cont)))) := 
      @Monoid_map (alist var) _ _ (@Monoid_set_union _ _ _ _) _ _.

    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Contexts_m : MonadWriter monoid m}.
    Context {MonadExc_m : MonadExc string m}.
    Context {ContSubst_m : MonadReader (alist cont cont) m}.

(*
    Fixpoint term_cont (e : exp) : m lset (@eq cont).
    refine (
      match e with
        | AppK_e k _ => singleton k
        | App_e _ ks _ => reduce Sets.empty Sets.singleton Sets.union ks
        | Halt_e _ _ => Sets.empty
        | Switch_e _ arms def =>
          let arm_ks :=
            reduce Sets.empty 
                   (fun pe => let '(p,e) := pe in term_cont e)
                   Sets.union arms in
          let def_ks :=
            match def with
              | None => Sets.empty
              | Some e => term_cont e
            end
          in
          Sets.union arm_ks def_ks
        | Let_e (Fn_d v ks xs e') e => _
        | Let_e _ e => term_cont e
        | Letrec_e _ _ => _
        | LetK_e ks e => _
      end).
*)

    Definition call (f : op) (ks : list cont) : m unit :=
      match f with
        | Var_o f =>
          tell (Maps.singleton f (Sets.singleton ks))
        | _ => raise "Calling non-variable"%string
      end.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Definition isSingleton {A} (ls : lset (@eq A)) : option A :=
      match ls with
        | x :: nil => Some x
        | _ => None
      end.
    
    Fixpoint replaceCalls (f : op) (k : cont) (e : exp) : exp :=
      match e with
        | App_e f' ks xs => if eq_dec f f' then AppK_e k xs else e
        | AppK_e _ _ => e
        | Halt_e _ _ => e
        | Let_e d e => Let_e d (replaceCalls f k e)
        | LetK_e ks e =>
          let ks' := map (fun kxse => let '(k,xs,e) := kxse in
            (k, xs, replaceCalls f k e)) ks
          in 
          LetK_e ks' (replaceCalls f k e)
        | Letrec_e ds e =>
          Letrec_e ds (replaceCalls f k e)
        | Switch_e o arms def =>
          let arms' := map (fun x => (fst x, replaceCalls f k (snd x))) arms in
          let def' := map (replaceCalls f k) def in
          Switch_e o arms' def'
      end.

    Definition var_to_cont (v : var) : m cont :=
      ret match v with 
            | Anon_v p => K "" p
            | Named_v s None => K s 1
            | Named_v s (Some p) => K s p
          end.

    Definition contify_k (k : cont) : m cont :=
      k' <- asks (Maps.lookup k) ;;
      match k' with
        | None => ret k
        | Some k => ret k
      end.
        
    Fixpoint withConts {T} (ks ks' : list cont) (c : m T) : m T :=
      match ks , ks' with
        | nil , nil => c
        | k :: ks , k' :: ks' => local (Maps.add k k') (withConts ks ks' c)
        | _ , _ => raise "inconsistent continutations "%string
      end.

    Fixpoint contify_exp (e : exp) : m exp.    
    refine (
      match e with
        | AppK_e k xs =>
          k <- contify_k k ;;
          ret (AppK_e k xs)
        | App_e f ks xs => 
          ks <- mapM contify_k ks ;;
          call f ks ;;
          ret (App_e f ks xs)
        | Halt_e x w => 
          ret (Halt_e x w) 
        | Switch_e o arms def =>
          arms' <- mapM (fun pe => let '(p,e) := pe in 
            e' <- contify_exp e ;;
            ret (p, e')) arms ;;
          def' <- mapM contify_exp def ;;
          ret (Switch_e o arms' def')
        | Let_e (Fn_d f ks xs e_body) e =>
          e'_conts <- censor (Maps.remove f) (listens (Maps.lookup f) (contify_exp e)) ;;
          let '(e',conts) := e'_conts in
          match conts with
            | None =>
              (* f is either dead or only passed forward, we can't contify it *)
              e_body' <- contify_exp e_body ;;
              ret (Let_e (Fn_d f ks xs e_body') e')
            | Some conts =>
              match isSingleton conts with
                | None => 
                  (** We can't contify f **)
                  e_body' <- contify_exp e_body ;;
                  ret (Let_e (Fn_d f ks xs e_body') e')
                | Some args =>
                  (** We can contify f **)
                  k <- var_to_cont f ;;
                  let e' := replaceCalls (Var_o f) k e' in
                  e_body' <- withConts ks args (contify_exp e_body) ;;
                  ret (LetK_e ((k, xs, e_body') :: nil) e')
              end
          end
        | Let_e d e => 
          e' <- contify_exp e ;;
          ret (Let_e d e')
        | Letrec_e ds e =>
          (** ignore for now **)
          e' <- contify_exp e ;;
          ret (Letrec_e ds e')          
        | LetK_e ks e =>
          ks' <- mapM (fun kxse => let '(k,xs,e) := kxse in
            e' <- contify_exp e ;;
            ret (k, xs, e')) ks ;;
          e' <- contify_exp e ;;
          ret (LetK_e ks' e')
      end).
    Defined.
  End monadic.


End Contify.
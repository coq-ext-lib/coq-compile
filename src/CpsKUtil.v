Require Import CoqCompile.CpsK.
Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Lists.
Require Import Bool ZArith.

Set Implicit Arguments.
Set Strict Implicit.

Import CPSK.

  (** returns the function name f if [fun x => e] is a simple eta expansion of the form
     [fun x => f x]. *)
  Definition match_eta (k':cont) (x:var) (e:exp) : option op := 
    match e with 
      | App_e op1 (k::nil) ((Var_o y)::nil) => 
        if eq_dec y x && eq_dec k k' then Some op1 else None
      | _ => None
    end.
  
  Fixpoint eq_vars_ops (xs:list var) (vs:list op) : bool := 
    match xs, vs with 
      | nil, nil => true
      | x::xs, (Var_o y)::vs => eq_dec x y && eq_vars_ops xs vs
      | _, _ => false
    end.
  
  (** similar to the above, but for the general case of [fun (x1,...,xn) => e] being an
     eta-expansion of [fun (x1,...,xn) => f(x1,...,xn)]. *)
  Definition match_etas (ks : list cont) (xs:list var) (e:exp) : option op := 
    match e with 
      | App_e op1 k ys =>
        if eq_dec k ks && eq_vars_ops xs ys then Some op1 else None
      | _ => None
    end.
  
  (** Let-bind [xi] to [#i v] for the expression [e].  This is used in the compilation
      of pattern matching below. *)
  Fixpoint bind_proj(v:op)(xs:list var)(offset:Z)(e:exp) : exp := 
    match xs with 
      | nil => e
      | x::xs => Let_e (Prim_d x Proj_p ((Int_o offset)::v::nil)) (bind_proj v xs (1+offset) e)
    end.


Section free.
  Variable v : var + cont.

  Definition free_in_var (o : var) : bool :=
    match v with
      | inl v => eq_dec v o
      | _ => false
    end.

  Definition defined_by (d : decl) : bool :=
    match v with
      | inl v =>
        match d with
          | Op_d v' _ => eq_dec v v'
          | Prim_d v' _ _ => eq_dec v v'
          | Fn_d v' _ _ _ => eq_dec v v'
          | Bind_d a b _ _ => eq_dec a v || eq_dec b v
        end
      | inr _ => false
    end.

  Definition free_in_op (o : op) : bool :=
    match v with
      | inl v =>
        match o with
          | Var_o v' => eq_dec v v'
          | Int_o _ => false
          | Con_o _ => false
          | InitWorld_o => false
        end
      | _ => false
    end.

  Definition free_in_k (c : cont) : bool :=
    match v with 
      | inl _ => false
      | inr x => eq_dec x c
    end.

  Fixpoint free_in_exp (e : exp) : bool :=
    match e with
      | App_e f ks xs =>
        free_in_op f || anyb free_in_k ks || allb free_in_op xs
      | AppK_e k xs =>
        free_in_k k || allb free_in_op xs
      | Let_e ds e =>
        if defined_by ds then false
          else if free_in_decl ds then true else free_in_exp e
      | LetK_e ks e =>
        if anyb (fun x => let '(k,_,_) := x in free_in_k k) ks then false
        else free_in_exp e || anyb (fun x => let '(_, vs, e) := x in
          (if anyb free_in_var vs then false else free_in_exp e)) ks
      | Letrec_e ds e =>
        if anyb defined_by ds then false
        else if anyb free_in_decl ds then true else free_in_exp e
      | Switch_e o br def =>
        if free_in_op o then
          if allb (fun x => free_in_exp (snd x)) br
            then match def with 
                   | None => true
                   | Some e => free_in_exp e
                 end
            else
              false
          else
            false
      | Halt_e o1 o2 =>
        orb (free_in_op o1) (free_in_op o2)
    end
  with free_in_decl (d : decl) : bool :=
    match d with
      | Op_d _ o => free_in_op o
      | Prim_d _ _ vs => anyb free_in_op vs
      | Bind_d _ _ _ vs => anyb free_in_op vs
      | Fn_d _ ks vs e =>
        if anyb free_in_k ks || anyb free_in_var vs then false
          else free_in_exp e
    end.
End free.
  

Section free_vars.
  (** list is suboptimal here **)
  Require Import ExtLib.Structures.Monads.
  Require Import ExtLib.Structures.Folds.
  Require Import ExtLib.Structures.Reducible.
  Require Import ExtLib.Structures.Monoid.
  Require Import ExtLib.Structures.Sets.
  Require Import ExtLib.Data.Monads.IdentityMonad.
  Require Import ExtLib.Data.Monads.WriterMonad.
  Section with_sets.
    Variable s : Type.
    Context {DSet_s : DSet s (@eq (var + cont))}.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Writer_m : MonadWriter (Monoid_set_union (R := @eq (var + cont))) m}.

    Definition free_vars_op (o : op) : m unit :=
      match o with
        | Var_o v => tell (singleton (inl v))
        | _ => ret tt
      end.

    Definition free_vars_k (k : cont) : m unit :=
      tell (singleton (inr k)).

    Import MonadNotation.
    Local Open Scope monad_scope.

    (** remove elements of v **)
    Definition filter_vars (v : list var) : s -> s :=
      filter (fun x => negb (anyb (fun y => eq_dec x (inl y)) v)).

    Definition filter_conts (v : list cont) : s -> s :=
      filter (fun x => negb (anyb (fun y => eq_dec x (inr y)) v)).

    Fixpoint free_vars_exp' (e : exp) : m unit :=
      match e with
        | App_e f ks xs => 
          free_vars_op f ;;
          iterM free_vars_k ks ;;
          iterM free_vars_op xs
        | AppK_e k xs =>
          free_vars_k k ;;
          iterM free_vars_op xs
        | LetK_e ks e =>
          censor (filter_conts (map (fun x => let '(k,_,_) := x in k) ks))
            (iterM (fun x => let '(k,xs,e) := x in 
              censor (filter_vars xs) (free_vars_exp' e)) ks ;;
             free_vars_exp' e)
        | Halt_e o1 o2 =>
          free_vars_op o1 ;;
          free_vars_op o2
        | Let_e ds e =>
          free_vars_decl' false ds ;;
          censor (filter (fun x => negb (defined_by x ds))) (free_vars_exp' e)
        | Letrec_e ds e =>
          censor (filter (fun x => negb (anyb (defined_by x) ds)))
                 (iterM (free_vars_decl' true) ds ;; free_vars_exp' e)
        | Switch_e o arms def =>
          free_vars_op o ;;
          mapM (fun x => free_vars_exp' (snd x)) arms ;;
          match def with
            | None => ret tt
            | Some e => free_vars_exp' e
          end        
      end
    with free_vars_decl' (rec : bool) (d : decl) : m unit :=
      match d with
        | Op_d v o =>
          if rec then
            censor (filter (fun x => negb (eq_dec (inl v) x))) (free_vars_op o)
          else
            free_vars_op o
        | Prim_d v p os =>
          if rec then 
            censor (filter (fun x => negb (eq_dec (inl v) x))) (mapM free_vars_op os) ;; ret tt
          else 
            iterM free_vars_op os
        | Bind_d x w m os =>
          iterM free_vars_op os 
        | Fn_d v ks xs e =>
          censor (filter (fun x => negb (orb (anyb (fun v => eq_dec x (inl v)) xs) (anyb (fun v => eq_dec x (inr v)) ks))))
            (if rec then
              censor (filter (fun x => negb (eq_dec (inl v) x))) (free_vars_exp' e)
             else 
              free_vars_exp' e)
      end.
  End monadic.

  Definition free_vars_exp (e : exp) : s :=
    unIdent (execWriterT (free_vars_exp' e)).

  Definition free_vars_decl (r : bool) (d : decl) : s :=
    unIdent (execWriterT (free_vars_decl' r d)).

  Definition free_vars_cont (k : cont) (xs : list var) (e : exp) : s :=
    unIdent (execWriterT (censor (filter_vars xs) (free_vars_exp' e))).

  End with_sets.

End free_vars.

Section tuples_fun.
  Require Import ExtLib.Data.Map.FMapAList.
  Require Import ExtLib.Data.Set.ListSet.

  Fixpoint tuples_arity_exp' (e:exp) (dom:alist var nat) : alist var nat :=
    match e with
      | App_e o ks os => dom
      | Let_e d e => 
        let dom' := tuples_arity_decl' d dom in
        tuples_arity_exp' e dom'
      | Letrec_e ds e => 
        let dom' := List.fold_left (fun acc d => tuples_arity_decl' d acc) ds dom in
        tuples_arity_exp' e dom'
      | Switch_e o arms def =>
        let init := match def with
                      | Some e => tuples_arity_exp' e dom
                      | None => dom
                    end in
        List.fold_left (fun acc x => let '(p,e) := x in tuples_arity_exp' e acc) arms init
      | Halt_e o1 o2 => dom
      | AppK_e k os => dom
      | LetK_e kves e => 
        let dom' := List.fold_left (fun acc x => let '(k, xs, e) := x in 
          tuples_arity_exp' e acc) kves dom in
        tuples_arity_exp' e dom'
    end
  with tuples_arity_decl' (d:decl) (dom:alist var nat) : alist var nat :=
    match d with
      | Op_d x o => dom
      | Prim_d x p os => match p with
                          | MkTuple_p => Maps.add x (length os) dom
                          | _ => dom
                        end
      | Fn_d v ks xs e => tuples_arity_exp' e dom
      | Bind_d x w m os => dom
    end.
  
  Definition tuples_arity_exp (e:exp) : alist var nat :=
    tuples_arity_exp' e Maps.empty.

  Definition tuples_arity_decl (d:decl) : alist var nat :=
    tuples_arity_decl' d Maps.empty.

  Definition tuples_in_exp (e:exp) : lset (@eq var) :=
    Maps.keys _ _ (tuples_arity_exp e).

  Definition tuples_in_decl (d:decl) : lset (@eq var) :=
    Maps.keys _ _ (tuples_arity_decl d).

End tuples_fun.
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
    let x := unIdent (runWriterT (free_vars_exp' e)) in
    snd x.

  Definition free_vars_decl (r : bool) (d : decl) : s :=
    let x := unIdent (runWriterT (free_vars_decl' r d)) in
    snd x.
  End with_sets.

End free_vars.

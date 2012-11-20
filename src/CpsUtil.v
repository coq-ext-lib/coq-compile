Require Import CoqCompile.Cps.
Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Lists.
Require Import Bool ZArith.

Set Implicit Arguments.
Set Strict Implicit.

Import CPS.

  (** returns the function name f if [fun x => e] is a simple eta expansion of the form
     [fun x => f x]. *)
  Definition match_eta (x:var) (e:exp) : option op := 
    match e with 
      | App_e op1 ((Var_o y)::nil) => 
        if eq_dec y x then Some op1 else None
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
  Definition match_etas (xs:list var) (e:exp) : option op := 
    match e with 
      | App_e op1 ys =>
        if eq_vars_ops xs ys then Some op1 else None
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
  Variable v : var.

  Fixpoint defined_by (d : decl) : bool :=
    match d with
      | Op_d v' _ => eq_dec v v'
      | Prim_d v' _ _ => eq_dec v v'
      | Fn_d v' _ _ => eq_dec v v'
      | Bind_d a b _ _ => eq_dec a v || eq_dec b v
    end.

  Definition free_in_op (o : op) : bool :=
    match o with
      | Var_o v' => eq_dec v v'
      | Int_o _ => false
      | Con_o _ => false
    end.

  Fixpoint free_in_exp (e : exp) : bool :=
    match e with
      | App_e f xs =>
        if free_in_op f then true else allb free_in_op xs
      | Let_e ds e =>
        if defined_by ds then false
          else if free_in_decl ds then true else free_in_exp e
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
        andb (free_in_op o1) (free_in_op o2)
    end
  with free_in_decl (d : decl) : bool :=
    match d with
      | Op_d _ o => free_in_op o
      | Prim_d _ _ vs => anyb free_in_op vs
      | Bind_d _ _ _ vs => anyb free_in_op vs
      | Fn_d _ vs e =>
        if anyb (eq_dec v) vs then false
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
    Context {DSet_s : DSet s (@eq var)}.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Writer_m : MonadWriter (Monoid_set_union (R := @eq var)) m}.

    Definition free_vars_op (o : op) : m unit :=
      match o with
        | Var_o v => tell (singleton v)
        | _ => ret tt
      end.
    Import MonadNotation.
    Local Open Scope monad_scope.

    Fixpoint free_vars_exp' (e : exp) : m unit :=
      match e with
        | App_e f xs => 
          free_vars_op f ;;
          mapM free_vars_op xs ;;
          ret tt
        | Halt_e o1 o2 =>
          free_vars_op o1 ;;
          free_vars_op o2
        | Let_e ds e =>
          free_vars_decl' false ds ;;
          censor (filter (fun x => negb (defined_by x ds))) (free_vars_exp' e)
        | Letrec_e ds e =>
          iterM (free_vars_decl' true) ds ;;
          censor (filter (fun x => negb (anyb (defined_by x) ds))) (free_vars_exp' e)
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
(*        | Rec_d ds => 
          mapM (free_vars_decl' true) ds ;;
          ret tt
*)
        | Op_d v o =>
          if rec then
            censor (filter (fun x => negb (eq_dec v x))) (free_vars_op o)
          else
            free_vars_op o
        | Prim_d v p os =>
          if rec then 
            censor (filter (fun x => negb (eq_dec v x))) (mapM free_vars_op os) ;; ret tt
          else 
            iterM free_vars_op os
        | Bind_d x w m os =>
          iterM free_vars_op os 
        | Fn_d v xs e =>
          if rec then
            censor (filter (fun x => negb (eq_dec v x || anyb (eq_dec x) xs))) (free_vars_exp' e)
          else 
            censor (filter (fun x => negb (anyb (eq_dec x) xs))) (free_vars_exp' e)
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

Require Import CoqCompile.Cps.
Require Import List.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Import CPS.

Section AllB.
  Variable T : Type.
  Variable p : T -> bool.

  Fixpoint allb (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls =>
        if p l then allb ls else false
    end.

  Fixpoint anyb (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls =>
        if p l then true else anyb ls
    end.
End AllB.

Section free.
  Variable v : var.

  Fixpoint defined_by (d : decl) : bool :=
    match d with
      | Op_d v' _ => eq_dec v v'
      | Prim_d v' _ _ => eq_dec v v'
      | Fn_d v' _ _ => eq_dec v v'
      | Rec_d ds => anyb defined_by ds
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
          else if free_in_exp e then true else free_in_decl ds
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
      | Halt_e o =>
        free_in_op o
    end
  with free_in_decl (d : decl) : bool :=
    match d with
      | Op_d _ o => free_in_op o
      | Prim_d _ _ vs => anyb free_in_op vs
      | Fn_d _ vs e =>
        if anyb (eq_dec v) vs then false
          else free_in_exp e
      | Rec_d ds =>
        anyb free_in_decl ds
    end.
End free.
  

Section free_vars.
  (** list is suboptimal here **)
  Require Import ExtLib.Monad.Monad.
  Require Import ExtLib.Monad.WriterMonad.
  Require Import ExtLib.Monad.IdentityMonad.
  Require Import ExtLib.Monad.Folds.
  Require Import ExtLib.Data.Monoid.
  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context { Writer_m : Writer (@Monoid_list_union var _) m}.

    Definition free_vars_op (o : op) : m unit :=
      match o with
        | Var_o v => tell (v :: nil)
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
        | Halt_e o =>
          free_vars_op o
        | Let_e ds e =>
          free_vars_decl' false ds ;;
          censor (filter (fun x => negb (defined_by x ds))) (free_vars_exp' e)
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
        | Rec_d ds => 
          mapM (free_vars_decl' true) ds ;;
          ret tt
        | Op_d v o =>
          if rec then
            censor (filter (fun x => negb (eq_dec v x))) (free_vars_op o)
          else
            free_vars_op o
        | Prim_d v p os =>
          if rec then 
            censor (filter (fun x => negb (eq_dec v x))) (mapM free_vars_op os) ;; ret tt
          else 
            mapM free_vars_op os ;; ret tt
        | Fn_d v xs e =>
          if rec then
            censor (filter (fun x => negb (eq_dec v x || anyb (eq_dec x) xs))) (free_vars_exp' e)
          else 
            censor (filter (fun x => negb (anyb (eq_dec x) xs))) (free_vars_exp' e)
      end.
  End monadic.

  Definition free_vars_exp (e : exp) : list var :=
    let x := unIdent (runWriterT (free_vars_exp' e)) in
    snd x.

  Definition free_vars_decl (r : bool) (d : decl) : list var :=
    let x := unIdent (runWriterT (free_vars_decl' r d)) in
    snd x.

End free_vars.

Require Import CoqCompile.CpsK.
Require Import CoqCompile.CpsKUtil.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section DEADCODE.
  Import CPSK.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition Count := alist (var + cont) nat.

  Definition Monoid_Count : Monoid Count :=
  {| monoid_unit := Maps.empty
   ; monoid_plus := fun x y => Maps.combine (fun k x y => x + y) x y
  |} .

  Section monadic.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {State_m : MonadWriter Monoid_Count m}.

  Definition useV (v : var) : m unit :=
    tell (Maps.singleton (inl v) 1).
  (* modify (Monoid_Count.(monoid_plus) (Maps.singleton (inl v) 1)) ;; ret tt. *)

  Definition useC (v : cont) : m unit :=
    tell (Maps.singleton (inr v) 1).
(*
    modify (Monoid_Count.(monoid_plus) (Maps.singleton (inr v) 1)) ;; ret tt. *)

  Definition useOp (o : op) : m unit :=
    match o with
      | Var_o v => useV v
      | _ => ret tt
    end.

  Definition checkUse {T U} (c : m T) (test : Count -> bool) (no : T -> m U) (yes : T -> m U) : m U.
  refine (
    x <- listen c ;;
    if test (snd x) then 
      yes (fst x)
    else
      no (fst x)
  ).
  Defined.

  Definition ignore {T} (ls : list (var + cont)) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove x mp) ls).

  Definition ignoreVs {T} (ls : list var) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove (inl x) mp) ls).

  Definition ignoreKs {T} (ls : list cont) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove (inr x) mp) ls).

  Definition used (v : var + cont) (c : Count) : bool :=
    match Maps.lookup v c with
      | None => false
      | Some 0 => false
      | _ => true
    end.

  Fixpoint dce_exp (e : exp) : m exp :=
    match e with
      | App_e x ks xs =>
        useOp x ;; iterM useOp xs ;; iterM useC ks ;;
        ret (App_e x ks xs)
      | Let_e d e =>
        checkUse (dce_exp e) 
          (fun cts => 
            match d with
              | Fn_d x _ _ _ => used (inl x) cts
              | Op_d x _ => used (inl x) cts
              | Bind_d x w _ _ => orb (used (inl x) cts) (used (inl w) cts)
              | Prim_d x _ _ => used (inl x) cts
            end)
          (fun e => ret e)
          (fun e => 
            d <- dce_decl d ;;
            ret (Let_e d e))
      | Halt_e x y =>
        useOp x ;; useOp y ;; ret (Halt_e x y)
      | Switch_e o ps d => 
        ps <- mapM (fun p => let '(p,e) := p in
          e <- dce_exp e ;;
          ret (p, e)) ps ;;
        d <- mapM dce_exp d ;;
        useOp o ;;
        ret (Switch_e o ps d)
      | AppK_e k os =>
        iterM useOp os ;;
        useC k ;;
        ret (AppK_e k os)
      | LetK_e ks e =>
        checkUse (dce_exp e)
          (fun cts => true)
          (fun e => ret e)
          (fun e => 
            ks <- mapM (fun k => let '(k,xs,e) := k in
              e <- ignoreVs xs (dce_exp e) ;;
              ret (k, xs, e)) ks ;;
            ret (LetK_e ks e))
      | Letrec_e ds e =>
        let dsFvs := map (free_vars_decl true) ds in
        checkUse (dce_exp e)
          (fun cts => true)
          (fun e => ret e)
          (fun e => 
            ds <- mapM (fun d => dce_decl d) ds ;;
            ret (Letrec_e ds e))
    end
  with dce_decl (d : decl) : m decl :=
    match d with 
      | Fn_d x ks xs e =>
        e <- ignoreKs ks (ignoreVs xs (dce_exp e)) ;;
        ret (Fn_d x ks xs e)
      | Op_d x o =>
        useOp o ;; ret (Op_d x o)
      | Prim_d x p os => 
        iterM useOp os ;;
        ret (Prim_d x p os)
      | Bind_d x w m os =>
        iterM useOp os ;;
        ret (Bind_d x w m os)
    end.
  End monadic.

  Require Import ExtLib.Data.Monads.WriterMonad.
  Require Import ExtLib.Data.Monads.IdentityMonad.

  Definition dce (e : exp) : exp :=
    unIdent (evalWriterT (dce_exp (m := writerT _ ident) e)).

End DEADCODE.

Require Import CoqCompile.Lambda CoqCompile.Env.
Require Import ExtLib.Data.Strings.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.ZDecidables.
Require Import ExtLib.Core.PosDecidables.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Sets.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.Low.
Require Import CoqCompile.CpsKUtil.

Section maps.
  Variable map_var : Type -> Type.
  Context {FM : DMap Env.var map_var}.

Section monadic.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable State_blks : MonadState (list block) m.
  Variable Exc_m : MonadExc string m.
  (*
  Variable Mon_m : Monad m.
  Variable State_m : MonadState (nat * nat) m.
  Variable Reader_varmap : MonadReader (map_var lvar) m.
  Context {Reader_ctor_map : MonadReader (map_ctor Z) m}.
  Variable State_instrs : MonadState (LLVM.block) m.
  Variable State_blks : MonadState (list LLVM.block) m.
  Variable State_isExit : MonadState (option LLVM.label) m.
  *)

  Import CPSK.

  Definition prim2low (p:CpsCommon.primop) : option primop :=
    match p with
      | CpsCommon.Eq_p => Some Eq_p
      | CpsCommon.Neq_p => Some Neq_p
      | CpsCommon.Lt_p => Some Lt_p
      | CpsCommon.Lte_p => Some Lte_p
      | CpsCommon.Ptr_p => Some Ptr_p
      | CpsCommon.Plus_p => Some Plus_p
      | CpsCommon.Minus_p => Some Minus_p
      | CpsCommon.Times_p => Some Times_p
      | CpsCommon.MkTuple_p => None
      | CpsCommon.Proj_p => None
    end.

  Parameter freshVar : m var.
  Parameter freshLbl : m label.
  Definition opgen (o:op) : m op := ret o.
  Parameter emit_tm : term -> m unit.
  Parameter emit_instr : instr -> m unit.
  Parameter withNewCont : forall {T}, list (cont * label) -> m T -> m T.
  Parameter newBlock : label -> list var -> m unit -> m unit.
  Parameter inFreshLbl : list var -> m unit -> m label.
  Parameter tolowcont : cont -> m Low.cont.

  Definition gen_lbl_args (e:exp) : m (list var) :=
    let vs := free_vars_exp (s := list (var + cont)) e in
    let vs := filter (fun x => match x with
                                 | inl _ => true
                                 | inr _ => false
                               end) vs in
    mapM (fun x => match x with
                     | inl x => ret x
                     | inr _ => raise "shouldn't happen"%string
                   end) vs.

  Fixpoint list_repeat {A} (n:nat) (a:A) : list A :=
    match n with
      | O => nil
      | S n => a :: list_repeat n a
    end.

  Definition decl2low (d:decl) : m unit :=
    match d with
      | Op_d x o => ret tt
      | Prim_d x p os =>
        match p with
          | CpsCommon.Eq_p => 
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Eq_p vs)
          | CpsCommon.Neq_p =>
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Neq_p vs)
          | CpsCommon.Lt_p =>
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Lt_p vs)
          | CpsCommon.Lte_p =>
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Lte_p vs)
          | CpsCommon.Ptr_p =>
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Ptr_p vs)
          | CpsCommon.Plus_p => 
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Plus_p vs)
          | CpsCommon.Minus_p => 
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Minus_p vs)
          | CpsCommon.Times_p => 
            vs <- mapM opgen os ;;
            emit_instr (Primop_i x Times_p vs)
          | MkTuple_p => 
            vs <- mapM opgen os ;;
            mtyp <- mapM (fun v => x <- freshVar ;; ret (x, Int_t, v)) vs ;;
            emit_instr (Malloc_i (map (fun x => let '(x, t, v) := x in (x, t)) mtyp)) ;;
            dummy <- mapM (fun x => let '(x, t, v) := x in
              emit_instr (Store_i t v 0 x)) mtyp ;;
            ret tt
          | Proj_p => 
            vs <- mapM opgen os ;;
            match vs with
              | CpsCommon.Int_o idx :: CpsCommon.Var_o v :: nil => 
                emit_instr (Load_i x (Struct_t (list_repeat (length vs) Int_t)) idx v)
              | _ => raise ("Proj_p requires exactly 2 arguments"%string)
            end
        end
      | Fn_d _ _ _ _ => raise ("Function found in closure converted body"%string) 
      | Bind_d _ _ m _ => match m with end
    end.
  
  Fixpoint cpsk2low (e:exp) : m unit.
  refine(
    match e with
      | App_e o ks os => 
        v <- opgen o ;;
        vs <- mapM opgen os ;;
        x <- freshVar ;;
        ks <- mapM tolowcont ks ;;
        emit_tm (Call_tm x v vs ks)
      | Let_e d e => 
        decl2low d ;;
        cpsk2low e
      | Letrec_e ds e => 
        mapM decl2low ds ;;
        cpsk2low e
      | Switch_e o arms e =>
        v <- opgen o ;;
        arms <- mapM (fun pat =>
          let '(p,e) := pat in
            lbl <- inFreshLbl nil (cpsk2low e) ;;
            ret (p, lbl, map (fun x => Var_o x) nil)) arms ;;
        defLbl <- match e with
                    | None => ret None
                    | Some e => 
                      lbl <- inFreshLbl nil (cpsk2low e) ;;
                      ret (Some (lbl, nil))
                  end ;;
        emit_tm (Switch_tm v arms None)
      | Halt_e o _ => 
        v <- opgen o ;;
        emit_tm (Halt_tm v)
      | AppK_e k os => 
        k <- tolowcont k ;;
        vs <- mapM opgen os ;;
        emit_tm (Cont_tm k vs)
      | LetK_e cves e => 
        wlbls <- mapM (fun x => let '(k, vs, e) := x in 
          l <- freshLbl ;;
          ret (k, vs, e, l)) cves ;;
        withNewCont 
          (map (fun x => let '(k, vs, e, l) := x in (k, l)) wlbls)
          ((mapM (fun x => let '(k, vs, e, l) := x in newBlock l vs (cpsk2low e)) wlbls) ;;
            cpsk2low e)
    end).
  Grab Existential Variables.
  (* wtf? *)

End monadic.
End maps.



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
Require Import ExtLib.Data.Map.FMapAList.

Section maps.
  Import CPSK.

  Variable map_var : Type -> Type.
  Context {FM_var : DMap Env.var map_var}.
  Variable map_cont : Type -> Type.
  Context {FM_cont : DMap CPSK.cont map_cont}.

Section monadic.
  Import MonadNotation.
  Local Open Scope monad_scope.



  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {State_blks : MonadState (list block) m}.
  Context {Exc_m : MonadExc string m}.
  Context {Fresh_m : MonadState positive m}.
  Context {Freshl_m : MonadState positive m}.
  Context {Block_m : MonadState (list (label * list var * list instr)) m}.
  Context {Blocks_m : MonadState (alist label block) m}.
  Context {VarMap_m : MonadReader (map_var var) m}.
  Context {ContMap_m : MonadReader (map_cont Low.cont) m}.

  Definition freshVar : m var :=
    x <- modify (MR := Fresh_m) (fun x => Psucc x) ;;
    ret (Env.Anon_v x).

  Definition freshLbl : m label :=
    l <- modify (MR := Freshl_m) (fun x => Psucc x) ;;
    ret ("l"++nat2string10 (nat_of_P l))%string.

  Definition emit_tm (tm : term) : m unit :=
    block_stack <- get (MonadState := Block_m) ;;
    match block_stack with
      | nil => raise "ERROR: No current block"%string
      | (l, vs, is) :: blks =>
        put blks ;;
        let blk := {| b_args := vs ; b_insns := rev is ; b_term := tm |} in
        modify (MR := Blocks_m) (Maps.add l blk) ;;
        ret tt
    end.

  Definition emit_instr (i : instr) : m unit :=
    block_stack <- get (MonadState := Block_m) ;;
    match block_stack with
      | nil => raise "ERROR: No current block"%string
      | (l, vs, is) :: blks =>
        put ((l, vs, i :: is) :: blks)
    end.

  Definition newBlock {T} (l : label) (vs : list var) (c : m T) : m T.
  refine (
    modify (fun blks => (l, vs, nil) :: blks) ;;
    c 
    ).
  Defined.

  Definition cont2low (c : CPSK.cont) : m Low.cont.
  refine (
    r <- asks (MR := ContMap_m) (Maps.lookup c) ;;
    match r with
      | Some r => ret r
      | None => raise "ERROR: Unknown continuation"%string
    end).
  Defined.

  Definition withNewCont (ks : list (CPSK.cont * label)) : forall {T}, m T -> m T.
  refine (
    @local _ _ ContMap_m (fold_left (fun acc x => Maps.add (map := map_cont) (fst x) (inr (snd x)) acc) ks)).
  Defined.
  
  (* Doesn't this definition of inFreshLbl cause the terminating switch in cpsk2low
   * to be emitted in the default label block!? *)
  Definition inFreshLbl (vs:list var) (k:m unit) : m label :=
    l <- freshLbl ;;
    block_stack <- get (MonadState := Block_m) ;;
    put ((l, vs, nil) :: block_stack) ;;
    k ;;
    ret l.

  Definition opgen (o:op) : m op :=
    match o with 
      | Var_o v => 
        x <- asks (Maps.lookup v) ;;
        match x with
          | None => raise "ERROR: Unknown variable"%string
          | Some v => ret (Var_o v)
        end
      | Con_o c => ret (Con_o c)
      | Int_o z => ret (Int_o z)
    end.

  Definition gen_lbl_args (e:exp) : m (list var) :=
    let vs := free_vars_exp (s := list (var + cont)) e in
    let vs := filter (fun x => match x with
                                 | inl _ => true
                                 | inr _ => false
                               end) vs in
    mapM (fun x => match x with
                     | inl x => ret x
                     | inr _ => raise "found continuation after filter"%string
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
  
  Fixpoint cpsk2low (e:exp) : m unit :=
    match e with
      | App_e o ks os => 
        v <- opgen o ;;
        vs <- mapM opgen os ;;
        x <- freshVar ;;
        ks <- mapM cont2low ks ;;
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
        emit_tm (Switch_tm v arms defLbl)
      | Halt_e o _ => 
        v <- opgen o ;;
        emit_tm (Halt_tm v)
      | AppK_e k os => 
        k <- cont2low k ;;
        vs <- mapM opgen os ;;
        emit_tm (Cont_tm k vs)
      | LetK_e cves e => 
        lbls <- mapM (fun x => let '(k, vs, e) := x in 
          l <- freshLbl ;;
          ret (k, l)) cves ;;
        withNewCont 
          (map (fun x => let '(k, l) := x in (k, l)) lbls)
          ((iterM (fun x => let '(k, vs, e) := x in 
            l <- cont2low k ;;
            match l with
              | inr l =>
                newBlock l vs (cpsk2low e) ;; ret tt
              | inl _ => raise "local cont references cont parameter"%string
            end) cves) ;;
            cpsk2low e)
    end.

End monadic.
End maps.




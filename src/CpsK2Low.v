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
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Programming.Show.

Section maps.
  Import CPSK.

  Variable map_var : Type -> Type.
  Context {FM_var : DMap Env.var map_var}.
  Variable map_cont : Type -> Type.
  Context {FM_cont : DMap CPSK.cont map_cont}.

  Definition lowBinder (d : decl) : var :=
    match d with
      | Prim_d x _ _ 
      | Fn_d x _ _ _ 
      | Bind_d x _ _ _
      | Op_d x _ => x
    end.

  Section monadic.
    Import MonadNotation.
    Local Open Scope monad_scope.
    Local Open Scope string_scope.

    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Exc_m : MonadExc string m}.
    Context {Fresh_m : MonadState positive m}.
    Context {Freshl_m : MonadState positive m}.
    Context {Block_m : MonadState (option (label * list var * list instr)) m}.
    Context {Blocks_m : MonadState (alist label block) m}.
    Context {VarMap_m : MonadReader (map_var op) m}.
    Context {ContMap_m : MonadReader (map_cont Low.cont) m}.

    Definition freshVar : m var :=
      x <- modify (MS := Fresh_m) (fun x => Psucc x) ;;
      ret (Env.Anon_v x).
    Definition freshLbl : m label :=
      l <- modify (MS := Freshl_m) (fun x => Psucc x) ;;
      ret ("l"++nat2string10 (nat_of_P l))%string.

    Definition emit_tm (tm : term) : m block :=
      block_stack <- get (MonadState := Block_m) ;;
      match block_stack with
        | None => raise "BUG: No current block"%string
        | Some (l, vs, is) =>
          put None ;;
          let blk := {| b_args := vs ; b_insns := rev is ; b_term := tm |} in
            ret blk
      end.

    Definition emit_instr (i : instr) : m unit :=
      block_stack <- get (MonadState := Block_m) ;;
      match block_stack with
        | None => raise "BUG: No current block"%string
        | Some (l, vs, is) =>
          put (Some (l, vs, i :: is))
      end.

    Definition add_block (l : label) (blk : block) : m unit :=
      modify (MS := Blocks_m) (Maps.add l blk) ;;
      ret tt.

    Definition newBlock {T} (l : label) (vs : list var) (c : m T) : m T :=
      old_blk <- get (MonadState := Block_m) ;;
      put (Some (l, vs, nil)) ;;
      result <- c ;;
      put old_blk ;;
      ret result.

    Definition cont2low (c : CPSK.cont) : m Low.cont :=
      r <- asks (MR := ContMap_m) (Maps.lookup c) ;;
      match r with
        | Some r => ret r
        | None => raise ("ERROR: Unknown continuation '" ++ runShow (show c) ++ "'")
      end.

    Definition withNewConts (ks : list (CPSK.cont * label)) : forall {T}, m T -> m T :=
      @local _ _ ContMap_m (fold_left (fun acc x => Maps.add (map := map_cont) (fst x) (inr (snd x)) acc) ks).

    Definition withNewVars (vo : list (var * op)) : forall {T}, m T -> m T :=
      @local _ _ VarMap_m (fold_left (fun acc x => Maps.add (fst x) (snd x) acc) vo).

    Definition withNewVar (v : var) (o : op) : forall {T}, m T -> m T :=
      @withNewVars ((v,o) :: nil).
    
    Definition inFreshLbl {T} (vs:list var) (k:m T) : m (label * T) :=
      l <- freshLbl ;;
      result <- newBlock l vs k ;;
      ret (l, result).

    Definition opgen (o:op) : m op :=
      match o with 
        | Var_o v => 
          x <- asks (Maps.lookup v) ;;
          match x with
            | None => raise ("ERROR: Unknown variable '" ++ runShow (show v) ++ "'")
            | Some v => ret v
          end
        | Con_o _ => ret o
        | Int_o _ => ret o
        | InitWorld_o => ret o
      end.

    Definition gen_lbl_args (e:exp) : m (list var) :=
      let vs := free_vars_exp (s := list (var + cont)) e in
        let vs := filter (fun x => match x with
                                     | inl _ => true
                                     | inr _ => false
                                   end) vs in
        mapM (fun x => match x with
                         | inl x => ret x
                         | inr _ => raise "BUG: found continuation after filter"%string
                       end) vs.

    Fixpoint list_repeat {A} (n:nat) (a:A) : list A :=
      match n with
        | O => nil
        | S n => a :: list_repeat n a
      end.

    Definition decl2low (d:decl) {T} (c : m T) : m T :=
      match d with
        | Op_d x o => 
          withNewVar x o c
        | Prim_d x p os =>
          vs <- mapM opgen os ;;
          match p with
            | CpsCommon.Eq_p => 
              emit_instr (Primop_i x Eq_p vs)
            | CpsCommon.Neq_p =>
              emit_instr (Primop_i x Neq_p vs)
            | CpsCommon.Lt_p =>
              emit_instr (Primop_i x Lt_p vs)
            | CpsCommon.Lte_p =>
              emit_instr (Primop_i x Lte_p vs)
            | CpsCommon.Ptr_p =>
              emit_instr (Primop_i x Ptr_p vs)
            | CpsCommon.Plus_p => 
              emit_instr (Primop_i x Plus_p vs)
            | CpsCommon.Minus_p => 
              emit_instr (Primop_i x Minus_p vs)
            | CpsCommon.Times_p => 
              emit_instr (Primop_i x Times_p vs)
            | CpsCommon.MkTuple_p => 
              mtyp <- mapM (fun v => x <- freshVar ;; ret (x, Int_t, v)) vs ;;
              emit_instr (Malloc_i (map (fun x => let '(x, t, v) := x in (x, t)) mtyp)) ;;
              dummy <- mapM (fun x => let '(x, t, v) := x in
                emit_instr (Store_i t v 0 (Var_o x))) mtyp ;;
              ret tt
            | CpsCommon.Proj_p => 
              match vs with
                | CpsCommon.Int_o idx :: v :: nil => 
                (** TODO: Why do we require Int_o here? **)
                (** TODO: [length vs] is wrong here. **)
                  emit_instr (Load_i x (Struct_t (list_repeat (length vs) Int_t)) idx v)
                | _ => raise ("ERROR: Proj_p requires exactly 2 arguments"%string)
              end
          end ;;
          withNewVar x (Var_o x) c
        | Fn_d _ _ _ _ => raise ("ERROR: Function found in closure converted body"%string) 
        | Bind_d x _ mop _ => 
          match mop return m unit with end ;;
          withNewVar x (Var_o x) c
      end.
    
    Fixpoint cpsk2low' (e:exp) : m block :=
      match e with
        | App_e o ks os => 
          v <- opgen o ;;
          vs <- mapM opgen os ;;
          x <- freshVar ;;
          ks <- mapM cont2low ks ;;
          emit_tm (Call_tm x v vs ks)
        | Let_e d e => 
          decl2low d (cpsk2low' e)
        | Letrec_e ds e => 
          let binders : list (var * op) := map (fun d => let v := lowBinder d in (v, Var_o v)) ds in
          withNewVars binders
            (iterM (fun x => decl2low x (ret tt)) ds ;;
             cpsk2low' e)
        | Switch_e o arms e =>
          v <- opgen o ;;
          arms <- mapM (fun pat =>
            let '(p,e) := pat in
              lbl_blk <- inFreshLbl nil (cpsk2low' e) ;;
              add_block (fst lbl_blk) (snd lbl_blk) ;;
              ret (p, fst lbl_blk, map (fun x => Var_o x) nil)) arms ;;
          defLbl <- match e with
                      | None => ret None
                      | Some e => 
                        lbl_blk <- inFreshLbl nil (cpsk2low' e) ;;
                        add_block (fst lbl_blk) (snd lbl_blk) ;;
                        ret (Some (fst lbl_blk, nil))
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
          withNewConts
            (map (fun x => let '(k, l) := x in (k, l)) lbls)
            ((iterM (fun x => let '(k, vs, e) := x in 
              l <- cont2low k ;;
              match l with
                | inr l =>
                  blk <- newBlock l vs (withNewVars (map (fun x => (x, Var_o x)) vs) (cpsk2low' e)) ;;
                  add_block l blk
                | inl _ => raise "??: local cont references cont parameter"%string
              end) cves) ;;
            cpsk2low' e)
      end.

    Fixpoint tl_cpsk2low (e:exp) : m (label * block) :=
      lbl_blk <- inFreshLbl nil (cpsk2low' e) ;;
      add_block (fst lbl_blk) (snd lbl_blk) ;;
      ret lbl_blk.

  End monadic.

End maps.

Section monadic2.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {Exc_m : MonadExc string m}.

  Record StateData : Type :=
  { freshVar_p : positive
  ; freshLabel_p : positive
  ; curBlock : option (label * list var * list instr)
  ; allBlocks : alist label block
  }.
  Record ReaderData : Type :=
  { varMap : alist var op
  ; contMap : alist CPSK.cont Low.cont
  }.

  Definition MonadState_StateData_freshVar m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd freshVar_p 
    (fun x d => {| freshVar_p := x ; freshLabel_p := d.(freshLabel_p) ; curBlock := d.(curBlock) ; allBlocks := d.(allBlocks) |}).

  Definition MonadState_StateData_freshLabel_p m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd freshLabel_p 
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := x ; curBlock := d.(curBlock) ; allBlocks := d.(allBlocks) |}).

  Instance MonadState_StateData_curBlock m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd curBlock
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := d.(freshLabel_p) ; curBlock := x ; allBlocks := d.(allBlocks) |}).

  Instance MonadState_StateData_allBlocks m (M : Monad m) 
    : MonadState _ (stateT StateData m) :=
    StateProd allBlocks
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := d.(freshLabel_p) ; curBlock := d.(curBlock) ; allBlocks := x |}).

  Instance MonadReader_ReaderData_varMap m (M : Monad m) : MonadReader _ (readerT ReaderData m) :=
    ReaderProd varMap (fun x d => {| varMap := x ; contMap := d.(contMap) |}).

  Instance MonadReader_ReaderData_contMap m (M : Monad m) : MonadReader _ (readerT ReaderData m) :=
    ReaderProd contMap (fun x d => {| varMap := d.(varMap) ; contMap := x |}).

  Arguments tl_cpsk2low {_ _ _ _ m Mon MExc MSvar MSlbl _ _ _ _} (e) : rename.
  
  Definition tl_decl2low (name : var) (ks : list CPSK.cont) (args : list var) (tops : list (var * op)) (e : CPSK.exp) : m Low.function :=
    let c := tl_cpsk2low 
      (map_var := alist var) (FM_var := DMap_alist RelDec_var_eq)
      (map_cont := alist CPSK.cont) (FM_cont := DMap_alist CPSK.RelDec_cont_eq)
      (m := stateT StateData (readerT ReaderData m))
      (MSvar := MonadState_StateData_freshVar _ _)
      (MSlbl := MonadState_StateData_freshLabel_p _ _)
      e in
    let init_state : StateData := 
      {| freshVar_p := 1%positive
       ; freshLabel_p := 1%positive
       ; curBlock := None
       ; allBlocks := nil
       |}
    in
    let init_reader : ReaderData :=
      {| varMap := 
         let vars := fold_left (fun acc x => Maps.add (fst x) (snd x) acc) tops Maps.empty in
         fold_left (fun acc x => Maps.add x (Var_o x) acc) args vars
       ; contMap := (fix recur (ls : list CPSK.cont) idx (mp : alist CPSK.cont Low.cont) : alist CPSK.cont Low.cont := 
         match ls with
           | nil => mp 
           | l :: ls => 
             recur ls (S idx) (Maps.add l (inl idx) mp)
         end) ks 0 Maps.empty
       |}
    in
    c' <- runReaderT (runStateT c init_state) init_reader ;;
    let '(entry_label, _, state) := c' in
    ret {| f_name := name
         ; f_args := args
         ; f_conts := length ks
         ; f_body := state.(allBlocks)
         ; f_entry := entry_label |}.

  Definition cpsk2low (fs : list CPSK.decl) (e : CPSK.exp) : m Low.program :=
    let binders : list (var * op) := map (fun d => let v := lowBinder d in (v, Var_o v)) fs in
    fs <- mapM (fun d => 
      match d with
        | CPSK.Fn_d f ks args e => tl_decl2low f ks args binders e
        | _ => raise ("Decl other than function found in top-lvl")%string
      end) fs ;;
    entry <- tl_decl2low (Named_v "main"%string None) nil nil binders e ;;
    ret {| p_topdecl := entry::fs; p_entry := (Named_v "main"%string None) |}.

End monadic2.

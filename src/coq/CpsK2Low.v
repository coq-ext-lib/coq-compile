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
Require Import CoqCompile.TraceMonad.

Section maps.
  Import CPSK.

  Variable map_var : Type -> Type.
  Context {FM_var : DMap Env.var map_var}.
  Variable map_cont : Type -> Type.
  Context {FM_cont : DMap CPSK.cont map_cont}.
  Context {DS_cont : DSet (lset (@eq cont)) (@eq cont)}.
  Context {DS_var : DSet (lset (@eq var)) (@eq var)}.

  (* This is what happens when you suck at abstraction ... u use alists >.< *)
  Variable live : option (alist (var + cont) (lset (@eq (var + cont)))).
  Variable tup_arity : alist var nat.

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
    Context {Block_m : MonadState (option (label * list var * list var * list instr)) m}.
    Context {Blocks_m : MonadState (alist label block) m}.
    Context {VarMap_m : MonadReader (map_var op) m}.
    Context {ContMap_m : MonadReader (map_cont (Low.cont * list var)) m}.
    Context {TupVars_m : MonadState (lset (@eq var)) m}.
    Context {Trace_m : MonadTrace string m}.

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
        | Some (l, vs, ls, is) =>
          put None ;;
          let blk := {| b_args := vs ; b_scope := ls ; b_insns := rev is ; b_term := tm |} in
            ret blk
      end.

    Definition emit_instr (i : instr) : m unit :=
      block_stack <- get (MonadState := Block_m) ;;
      match block_stack with
        | None => raise "BUG: No current block"%string
        | Some (l, vs, ls, is) =>
          put (Some (l, vs, ls, i :: is))
      end.

    Definition add_block (l : label) (blk : block) : m unit :=
      modify (MS := Blocks_m) (Maps.add l blk) ;;
      ret tt.

    Definition withNewConts (ks : list (CPSK.cont * (Low.cont * list var))) : forall {T}, m T -> m T :=
      @local _ _ ContMap_m (fold_left (fun acc x => Maps.add (map := map_cont) (fst x) (snd x) acc) ks).

    Definition withNewVars (vo : list (var * op)) : forall {T}, m T -> m T :=
      @local _ _ VarMap_m (fold_left (fun acc x => Maps.add (fst x) (snd x) acc) vo).

    Definition withNewVar (v : var) (o : op) : forall {T}, m T -> m T :=
      @withNewVars ((v,o) :: nil).

    Definition newBlock {T} (l : label) (vs : list var) (ls : list var) (c : m T) : m T :=
      old_blk <- get (MonadState := Block_m) ;;
      put (Some (l, vs, ls, nil)) ;;
(*      let newVars := map (fun v => (v,Var_o v)) (vs ++ ls)%list in
      result <- local (fun _ => Maps.empty) (withNewVars newVars c) ;;*)
      result <- c ;;
      put old_blk ;;
      ret result.

    Context {SM : Show (map_var op)}.

    Definition opgen (o:op) : m op :=
      match o with 
        | Var_o v => 
          x <- asks (Maps.lookup v) ;;
          match x with
            | None => 
              m <- ask (T:=(map_var op)) ;;
              raise ("ERROR: Unknown variable '" ++ (to_string v) ++ "' in map " ++ (to_string m))
            | Some v => ret v
          end
        | Con_o _ => ret o
        | Int_o _ => ret o
        | InitWorld_o => ret (Con_o "False")
      end.

    Definition cont2low (c : CPSK.cont) : m (Low.cont * list op) :=
      r <- asks (MR := ContMap_m) (Maps.lookup c) ;;
      match r with
        | Some (k,vs) => 
          vs <- mapM (fun v => opgen (Var_o v)) vs ;;
          ret (k,vs)
        | None => raise ("ERROR: Unknown continuation '" ++ (to_string c) ++ "'")
      end.

    Definition inFreshLbl {T} (vs:list var) (ls:list var) (k:m T) : m (label * T) :=
      l <- freshLbl ;;
      result <- newBlock l vs ls k ;;
      ret (l, result).

    Fixpoint called_cont_exp (e : exp) : lset (@eq cont) :=
      match e with
        | Let_e _ e =>
          called_cont_exp e
        | Letrec_e _ e =>
          called_cont_exp e
        | Switch_e _ arms default =>
          let defaultKs := match default with
                             | None =>
                               Sets.empty
                             | Some e =>
                               called_cont_exp e
                           end in
          let armKs := map (fun a => let '(p,e) := a in called_cont_exp e) arms in
          fold Sets.union defaultKs armKs
        | AppK_e k _ =>
          Sets.singleton k
        | LetK_e ks e =>
          let calledKs := map (fun k => let '(_,_,e) := k in called_cont_exp e) ks in
          let eKs := called_cont_exp e in
          fold Sets.union eKs calledKs
        | _ => Sets.empty
      end.

    Definition cont_args (k : cont) : m (lset (@eq var)) :=
      r <- asks (MR := ContMap_m) (Maps.lookup k) ;;
      match r with
        | Some (_,vs) =>
          ret (fold (fun v acc => Sets.add v acc) Sets.empty vs)
        | None => 
          ret Sets.empty
      end.

    Definition gen_lbl_args (e:exp) : m (lset (@eq var)) :=
      let vs := free_vars_exp (s := lset (@eq (var + cont))) e in
      let vs := reduce Sets.empty (fun v => match v with
                                              | inl v => singleton v
                                              | _ => Sets.empty
                                            end) Sets.union vs in
      let ks := called_cont_exp e in
      reduceM (ret vs) cont_args (fun l r => ret (Sets.union l r)) ks.

    Fixpoint list_repeat {A} (n:nat) (a:A) : list A :=
      match n with
        | O => nil
        | S n => a :: list_repeat n a
      end.

    Definition nat_of_Z (z:Z) : nat :=
      match z with
        | Z0 => O
        | Zpos p => Pos.to_nat p
        | Zneg p => O
      end.

    Require Import Coq.Arith.Compare_dec.
    Definition updateVar {T} (x : Env.var) (vs : list op) (size:nat) (c : m T) : m T :=
      x <- opgen (Var_o x) ;;
      foldM (fun v idx => emit_instr (Store_i Int_t v idx x) ;; ret (idx + 1)%Z) 0%Z vs ;;
      if leb size (length vs) then c else 
        foldM (fun v idx => emit_instr (Store_i Int_t v idx x) ;; ret (idx + 1)%Z) 0%Z (list_repeat (size - length vs) (Int_o 0)) ;;
        c.

    Definition convertVars (input:lset (@eq Env.var)) : m (lset (@eq Env.var)) :=
      varMap <- ask ;;
      ret (fold (fun x acc => match Maps.lookup x varMap with
                                | Some (Var_o v) =>Sets.add v acc
                                | _ => acc
                              end) input Sets.empty).

    (*  size: length of the tuple we want
     *  v: program point
     *  e: remaining exp
     *  returns: a tuple variable and its size if its dead and can be used for a destructive update
     *)
    Definition updateable (size : nat) (v : var) (e : exp) : m (option (var * nat)) :=
      tup_vars <- get (MonadState := TupVars_m) ;;
      match live with
        | Some live' =>
          match Maps.lookup (K := var + cont) (inl v) live' with 
            | Some live_set =>
              let live_set : (lset (@eq Env.var)) := fold (fun x acc => 
                match x with
                  | inl v => Sets.add v acc
                  | inr _ => acc
                end) Sets.empty live_set in
              live_set <- convertVars live_set ;; 
              tup_vars <- convertVars tup_vars ;;
              let usable_vars := Sets.difference tup_vars live_set in
              let rando := fold (fun (x:var) acc => 
                match acc with
                  | Some v => Some v
                  | None => 
                    match Maps.lookup x tup_arity with
                      | Some size' => 
                        if leb size size' then Some (x,size') else None
                      | None => None
                    end
                end) None usable_vars in
              match rando with
                | None => 
                  mlog ("did not find a var " ++ "live: " ++ to_string live_set ++ " tups: " ++ to_string tup_vars)%string ;;
                  put (Sets.add v tup_vars) ;; ret None
                | Some (v',n) =>
                  mlog ("found a var " ++ "live: " ++ to_string live_set ++ " tups: " ++ to_string tup_vars)%string ;;
                  modify (Sets.add v) ;;
                  modify (Sets.remove v') ;;
                  ret (Some (v',n))
              end
            | None => put (Sets.add v tup_vars) ;; ret None
          end
        | None => put (Sets.add v tup_vars) ;; ret None
      end.

    Definition decl2low (d:decl) {T} (e : exp) (c : m T) : m T :=
      match d with
        | Op_d x o =>
          raise ("Must copy propagate before CpsK2Low: " ++ to_string d)%string
          (* withNewVar x o c *)
        | Prim_d x p os =>
          vs <- mapM opgen os ;;
          match p with
            | CpsCommon.Eq_p => 
              emit_instr (Primop_i x Eq_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Neq_p =>
              emit_instr (Primop_i x Neq_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Lt_p =>
              emit_instr (Primop_i x Lt_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Lte_p =>
              emit_instr (Primop_i x Lte_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Ptr_p =>
              emit_instr (Primop_i x Ptr_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Plus_p => 
              emit_instr (Primop_i x Plus_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Minus_p => 
              emit_instr (Primop_i x Minus_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.Times_p => 
              emit_instr (Primop_i x Times_p vs) ;; withNewVar x (Var_o x) c
            | CpsCommon.MkTuple_p => 
              updatable <- updateable (List.length vs) x e ;;
              match updatable with
                | None =>
                  emit_instr (Malloc_i ((x, (Struct_t (list_repeat (length vs) Int_t)))::nil)) ;;
                  foldM (fun v idx => emit_instr (Store_i Int_t v idx (Var_o x)) ;; ret (idx + 1)%Z) 0%Z vs ;;
                  withNewVar x (Var_o x) c
                | Some (v, size) =>
                  (** emit updates **)
                  x' <- opgen (Var_o v) ;;
                  updateVar v vs size (withNewVar x x' c)
              end
            | CpsCommon.Proj_p => 
              match vs with
                | CpsCommon.Int_o idx :: v :: nil => 
                  emit_instr (Load_i x (Struct_t (list_repeat (S (nat_of_Z idx)) Int_t)) idx v) ;; 
                  withNewVar x (Var_o x) c
                | _ => raise ("ERROR: Proj_p requires exactly 2 arguments  ["%string ++ (to_string os) ++ "] -> ["%string ++ (to_string vs) ++ "]"%string)
              end
          end 
        | Fn_d _ _ _ _ => raise ("ERROR: Function found in closure converted body"%string) 
        | Bind_d x w mop os => 
          vs <- mapM opgen os ;;
          match mop return m unit with 
            | PrintInt_m =>
              match os with
                | _ :: o :: nil =>
                  emit_instr (Bind_i x PrintInt_m (o :: nil))
                | _ =>
                  raise "ERROR: PrintInt_m with wrong arguments"
              end
            | PrintChar_m =>
              match os with
                | _ :: rs =>
                  emit_instr (Bind_i x PrintChar_m rs)
                | _ => 
                  raise "ERROR: PrintChar_m with wrong arguments"
              end
          end ;;
          withNewVars ((x, Var_o x)::(w, Int_o 1)::nil) c
      end.

    Definition getTuples (ds : list decl) : m (list (var * list op)) :=
      mapM (fun d =>
        match d with
          | Prim_d v MkTuple_p xs => ret (v, xs)
          | _ => raise "found non-tuple in letrec"
        end) ds.

    Fixpoint cpsk2low' (e:exp) : m block :=
      match e with
        | App_e o ks os =>
          v <- opgen o ;;
          vs <- mapM opgen os ;;
          x <- freshVar ;;
          ks <- mapM cont2low ks ;;
          emit_tm (Call_tm x v vs ks)
        | Let_e d e => 
          decl2low d e (cpsk2low' e)
        | Letrec_e ds e =>
          tpls <- getTuples ds ;;
          emit_instr (Malloc_i (map (fun x => (fst x, Struct_t (map (fun _ => Int_t) (snd x)))) tpls)) ;;
          withNewVars (map (fun x => (fst x, Var_o (fst x))) tpls) (
            iterM (fun x => let '(n, os) := x in
              vs <- mapM opgen os ;;
              foldM (fun v idx => emit_instr (Store_i Int_t v idx (Var_o n)) ;; ret (idx + 1)%Z) 0%Z vs ;;
              ret tt
            ) tpls ;;
            cpsk2low' e)
        | Switch_e o arms e =>
          v <- opgen o ;;
          arms <- mapM (fun pat =>
            let '(p,e) := pat in
              args <- gen_lbl_args e ;;
              lbl_blk <- inFreshLbl nil args (cpsk2low' e) ;;
              add_block (fst lbl_blk) (snd lbl_blk) ;;
              ret (p, fst lbl_blk, map (fun x => Var_o x) args)) arms ;;
          defLbl <- match e with
                      | None => ret None
                      | Some e => 
                        args <- gen_lbl_args e ;;
                        lbl_blk <- inFreshLbl nil args (cpsk2low' e) ;;
                        add_block (fst lbl_blk) (snd lbl_blk) ;;
                        ret (Some (fst lbl_blk, map (fun x => Var_o x) args))
                    end ;;
          emit_tm (Switch_tm v arms defLbl)
        | Halt_e o _ => 
          v <- opgen o ;;
          emit_tm (Halt_tm v)
        | AppK_e k os =>
          k <- cont2low k ;;
          let '(k,args) := k in
          vs <- mapM opgen os ;;
          emit_tm (Cont_tm k args vs)
        | LetK_e cves e => 
          lbls <- mapM (fun x => let '(k, vs, e) := x in 
            l <- freshLbl ;;
            vars <- gen_lbl_args e ;;
            let vars := filter (fun x => negb (existsb (fun y => eq_dec x y) vs)) vars in
            ret (k, (l,vars))) cves ;;
          withNewConts
            (map (fun x => let '(k,(l,v)) := x in (k,(inr l,v))) lbls)
            (iterM (fun x => let '(k, vs, e) := x in 
              l <- cont2low k ;;
              let '(l,_) := l in
              args <- gen_lbl_args e ;;
              let args := filter (fun x => negb (existsb (fun y => eq_dec x y) vs)) args in
              match l with
                | inr l =>
                  let newVars := (map (fun x => (x, Var_o x)) (args ++ vs))%list in
                  blk <- newBlock l vs args (withNewVars newVars (cpsk2low' e)) ;;
                  add_block l blk
                | inl _ => raise "??: local cont references cont parameter"%string
              end) cves ;;
             cpsk2low' e)
      end.

    Fixpoint tl_cpsk2low (e:exp) : m (label * block) :=
      args <- gen_lbl_args e ;;
      lbl_blk <- inFreshLbl nil args (cpsk2low' e) ;;
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
  Context {Trace_m : MonadTrace string m}.

  Record StateData : Type :=
  { freshVar_p : positive
  ; freshLabel_p : positive
  ; curBlock : option (label * list var * list var * list instr)
  ; allBlocks : alist label block
  ; tupVars : lset (@eq var)
  }.
  Record ReaderData : Type :=
  { varMap : alist var op
  ; contMap : alist CPSK.cont (Low.cont * list var)
  }.

  Definition MonadState_StateData_freshVar m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd freshVar_p 
    (fun x d => {| freshVar_p := x ; freshLabel_p := d.(freshLabel_p) ; curBlock := d.(curBlock) ; allBlocks := d.(allBlocks) ; tupVars := d.(tupVars) |}).

  Definition MonadState_StateData_freshLabel_p m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd freshLabel_p 
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := x ; curBlock := d.(curBlock) ; allBlocks := d.(allBlocks) ; tupVars := d.(tupVars) |}).

  Instance MonadState_StateData_curBlock m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd curBlock
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := d.(freshLabel_p) ; curBlock := x ; allBlocks := d.(allBlocks) ; tupVars := d.(tupVars) |}).

    Instance MonadState_StateData_tupInfo m (M : Monad m) : MonadState _ (stateT StateData m) :=
    StateProd tupVars
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := d.(freshLabel_p) ; curBlock := d.(curBlock) ; allBlocks := d.(allBlocks) ; tupVars := x |}).

  Instance MonadState_StateData_allBlocks m (M : Monad m) 
    : MonadState _ (stateT StateData m) :=
    StateProd allBlocks
    (fun x d => {| freshVar_p := d.(freshVar_p) ; freshLabel_p := d.(freshLabel_p) ; curBlock := d.(curBlock) ; allBlocks := x ; tupVars := d.(tupVars) |}).

  Instance MonadReader_ReaderData_varMap m (M : Monad m) : MonadReader _ (readerT ReaderData m) :=
    ReaderProd varMap (fun x d => {| varMap := x ; contMap := d.(contMap) |}).

  Instance MonadReader_ReaderData_contMap m (M : Monad m) : MonadReader _ (readerT ReaderData m) :=
    ReaderProd contMap (fun x d => {| varMap := d.(varMap) ; contMap := x |}).

  Arguments tl_cpsk2low {_ _ _ _ _ _ LIVE TUPS m Mon MExc MSvar MSlbl MStup MStrace _ _ _ _ _} (e) : rename.
 
  Definition tl_decl2low_h (live : option (alist (var + CPSK.cont) (lset (@eq (var + CPSK.cont))))) (name : var) (ks : list CPSK.cont) (args : list var) (tops : list (var * op)) (e : CPSK.exp) : m (Low.function) :=
    let c := tl_cpsk2low 
      (map_var := alist var) (FM_var := DMap_alist RelDec_var_eq)
      (map_cont := alist CPSK.cont) (FM_cont := DMap_alist CPSK.RelDec_cont_eq)
      (LIVE := live)  
      (TUPS := tuples_arity_exp e)  
      (m := stateT StateData (readerT ReaderData ( m)))
      (MSvar := MonadState_StateData_freshVar _ _)
      (MSlbl := MonadState_StateData_freshLabel_p _ _)
      e in
    let init_state : StateData := 
      {| freshVar_p := 1%positive
       ; freshLabel_p := 1%positive
       ; curBlock := None
       ; allBlocks := nil
       ; tupVars := nil
       |}
    in
    let init_reader : ReaderData :=
      {| varMap := 
         let vars := fold_left (fun acc x => Maps.add (fst x) (snd x) acc) tops Maps.empty in
         fold_left (fun acc x => Maps.add x (Var_o x) acc) args vars
       ; contMap := (fix recur (ls : list CPSK.cont) idx (mp : alist CPSK.cont (Low.cont * list var)) : alist CPSK.cont (Low.cont * list var) := 
         match ls with
           | nil => mp 
           | l :: ls => 
             recur ls (S idx) (Maps.add l (inl idx,nil) mp)
         end) ks 0 Maps.empty
       |}
    in
    c' <- runReaderT (runStateT c init_state) init_reader ;;
    let '(entry_label, _, state) := c' in
    ret ({| f_name := name
         ; f_args := args
         ; f_conts := length ks
         ; f_body := state.(allBlocks)
         ; f_entry := entry_label |}).

  Require Import CoqCompile.Opt.CopyPropCpsK.

  Definition cpsk2low_h (live : option (alist (var + CPSK.cont) (lset (@eq (var + CPSK.cont))))) (fs : list CPSK.decl) (e : CPSK.exp) : m Low.program :=
    let e := CopyProp.copyprop e in
    let binders : list (var * op) := map (fun d => let v := lowBinder d in (v, Var_o v)) fs in
    fs <- mapM (fun d => 
      match d with
        | CPSK.Fn_d f ks args e => 
          let e := CopyProp.copyprop e in
          tl_decl2low_h live f ks args binders e
        | _ => raise ("Decl other than function found in top-lvl")%string
      end) fs ;;
    entry <- tl_decl2low_h live (Named_v "coq_main"%string None) nil nil binders e ;;
    ret {| p_topdecl := entry::fs; p_entry := (Named_v "coq_main"%string None) |}.

  Definition cpsk2low : list CPSK.decl -> CPSK.exp -> m Low.program :=
    cpsk2low_h None.

  Definition cpsk2low_dupdate (live : alist (var + CPSK.cont) (lset (@eq (var + CPSK.cont)))) : list CPSK.decl -> CPSK.exp -> m Low.program :=
    cpsk2low_h (Some live).

End monadic2.


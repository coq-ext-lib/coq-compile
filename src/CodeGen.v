Require Import CoqCompile.Low.
Require Import CoqCompile.LLVM.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Map.FMapTwoThreeK.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Programming.Show.

Set Implicit Arguments.
Set Strict Implicit.

Definition lvar : Type := LLVM.var.
Notation "% x" := (LLVM.Local x) (at level 50).

Import MonadNotation.
Local Open Scope monad_scope.

Section sized.
  Variable WORD_SIZE : nat.
  Definition UNIVERSAL : LLVM.type := LLVM.I_t (8 * WORD_SIZE).
  Definition ADDR_SPACE : nat := 0.

  Definition CALLING_CONV := Some LLVM.X86_fastcallcc.
  Definition GC_NAME := Some "shadow-stack"%string.

  Definition PTR_TYPE := LLVM.Pointer_t ADDR_SPACE UNIVERSAL.

Section maps.
  Variable map_var : Type -> Type.
  Variable map_ctor : Type -> Type.
  Context {FM : DMap Env.var map_var}.
  Context {M_ctor : forall x, Reducible (map_ctor x) (constructor * x)}.
  Context {FM_ctor : DMap constructor map_ctor}.

  Variable map_lbl : Type -> Type.
  Context {Map_lbl : DMap label map_lbl}.
  Context {Foldable_lbl : forall a, Foldable (map_lbl a) (label * a)}.
  Definition CFG := map_lbl (list (label * list LLVM.value)).
  Definition Monoid_CFG : Monoid.Monoid CFG :=
    {| Monoid.monoid_plus := fun x y => Maps.combine (K := label) (fun k l r => l ++ r) x y
     ; Monoid.monoid_unit := Maps.empty |}.    

Section globals.
  Variable globals : map_var (LLVM.value * LLVM.type).

Section monadic.
  Variable m : Type -> Type.
  Context {Monad : Monad m}.
  Context {Exception : MonadExc string m}.
  Context {State_fresh : MonadState (nat * nat) m}.
  Context {Reader_varmap : MonadReader (map_var lvar) m}.
  Context {Reader_ctormap : MonadReader (map_ctor Z) m}.
  Context {Reader_baselimit : MonadReader (LLVM.var * LLVM.var) m}.
  Context {State_instrs : MonadState (LLVM.block) m}.
  Context {State_blks : MonadState (list LLVM.block) m}.
  Context {State_isExit : MonadState (option LLVM.label) m}.
  Context {Writer_cfg : MonadWriter Monoid_CFG m}.

  Definition freshVar (v : Env.var) : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
      put (S v_n, l_n) ;;
      ret (runShow (show v) (nat2string10 v_n))%string.     
  
  Definition freshLabel : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
      put (v_n, S l_n) ;;
      ret ("lbl" ++ nat2string10 l_n)%string.
  
  Definition withNewVar {T} (cps : Env.var) (llvm : LLVM.var) : m T -> m T :=
    local (MonadReader := Reader_varmap) (Maps.add cps llvm).
  
  Definition emitInstr (i : LLVM.instr) : m unit :=
    st <- get (MonadState := State_instrs) ;;
    let '(blbl, binstrs) := st in
      put (blbl, binstrs ++ i :: nil).

  Definition inLabel {T} (lbl : LLVM.label) (c : m T) : m T :=
    st <- get (MonadState := State_instrs) ;;
    put (Some lbl, nil) ;;
    t <- c ;;
    blk' <- get (MonadState := State_instrs) ;;
    blks <- get (MonadState := State_blks) ;;
    put (blk' :: blks) ;;
    put st ;;
    ret t.
  
  Definition inFreshLabel {T} (c : m T) : m (LLVM.label * T) :=
    lbl <- freshLabel ;;
    t <- inLabel lbl c ;;
    ret (lbl,t).

  Definition withLabel {T} (lbl : label) (c : m T) : m T :=
    inLabel lbl c.

  Definition getLabel : m LLVM.label :=
    block <- get (MonadState := State_instrs) ;;
    match fst block with
      | None => raise "Expected label for basic block"%string
      | Some lbl => ret lbl
    end.

  Definition addJump (to : label) (args : list LLVM.value) : m unit :=
    from <- getLabel ;;
    tell (Maps.singleton to ((from,args) :: nil)).

  Definition tagForConstructor (c : constructor) : m Z :=
    x <- ask (MonadReader := Reader_ctormap) ;;
    match Maps.lookup c x with
      | None => raise ("error looking for '" ++ c ++ "' in TODO" (*++ show_map x*))%string
      | Some z => ret z
    end.
  
  Definition emitExp (e : LLVM.exp) : m LLVM.var :=
    x <- freshVar (Env.Named_v "_"%string None) ;;
    emitInstr (LLVM.Assign_i (Some (LLVM.Local x)) e) ;;
    ret x.
  
  Definition castTo (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    match ty with
      | LLVM.Pointer_t _ _ => emitExp (LLVM.Inttoptr_e UNIVERSAL v ty)
      | _ => emitExp (LLVM.Bitcast_e UNIVERSAL v ty)
    end.
  
  Definition castFrom (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    match ty with
      | LLVM.Pointer_t _ _ =>
        emitExp (LLVM.Ptrtoint_e ty v UNIVERSAL)
      | _ =>
        emitExp (LLVM.Bitcast_e ty v UNIVERSAL)
    end.
  
  Definition opgen (op : op) : m LLVM.value :=
    match op with
      | Var_o v => 
        x <- ask ;;
        match Maps.lookup v x with
          | None => 
            match Maps.lookup v globals with
              | None => raise ("Couldn't find variable '" ++ runShow (show v) ++ "' in context")%string
              | Some (v,t) => 
                asLocal <- castFrom t v ;;
                ret (%asLocal)
            end
          | Some v =>
            ret (LLVM.Local v)
        end
      | Con_o c => 
        z <- tagForConstructor c ;;
        ret (LLVM.Constant (LLVM.Int_c z))
      | Int_o i => ret (LLVM.Constant (LLVM.Int_c i))
    end.

    Definition opgen_list2 (ls : list op) : m (LLVM.value * LLVM.value) :=
      match ls with
        | a :: b :: nil =>
          a <- opgen a ;;
          b <- opgen b ;;
          ret (a,b)
        | _ => 
          raise ("Expected 2 arguments got " ++ nat2string10 (length ls))%string
      end.
    
    Definition opgen_list1 (ls : list op) : m LLVM.value :=
      match ls with
        | a :: nil =>
          opgen a
        | _ => 
          raise ("Expected 1 arguments got " ++ nat2string10 (length ls))%string
      end.

  Definition generatePrim T (x : Env.var) (p : Low.primop) (os : list op) (k : m T) : m T :=
    match p with
      | Eq_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Eq UNIVERSAL l r) ;;
        withNewVar x y k
      | Neq_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL l r) ;;
        withNewVar x y k
      | Lt_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Slt UNIVERSAL l r) ;; (** Signed? **)
        withNewVar x y k
      | Lte_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Sle UNIVERSAL l r) ;;(** Signed? **)
        withNewVar x y k
          
      | Plus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Add_e false false UNIVERSAL l r ) ;;
        withNewVar x y k
      | Minus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Sub_e false false UNIVERSAL l r ) ;;
        withNewVar x y k
      | Times_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Mul_e false false UNIVERSAL l r ) ;;
        withNewVar x y k

      | Ptr_p => (* XXX Should use Select instruction *)
        p <- opgen_list1 os ;;
        y <- emitExp (LLVM.And_e UNIVERSAL p (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Zext_e (LLVM.I_t 1) (%y) UNIVERSAL) ;;
        y <- emitExp (LLVM.Shl_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Add_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        withNewVar x y k
    end.

  Definition getBase : m LLVM.var :=
    x <- ask (MonadReader := Reader_baselimit) ;;
    ret (fst x).

  Definition getLimit : m LLVM.var :=
    x <- ask (MonadReader := Reader_baselimit) ;;
    ret (snd x).

  Definition withBaseLimit {T} (base limit : LLVM.var) : m T -> m T :=                                                              
    local (MonadReader := Reader_baselimit) (fun _ => (base,limit)). 

  Fixpoint sizeof (t : primtyp) : nat :=
    match t with
      | Struct_t ts =>
        fold (fun t a => a + sizeof t) 0 ts
      | _ => WORD_SIZE
    end.

  Definition generateAlloca T (allocs : list (var * primtyp)) (k : m T) : m T :=
    let doAlloc alloc k :=
      let '(v,t) := alloc in
      let size := WORD_SIZE + sizeof t in
      addr <- emitExp (LLVM.Alloca_e UNIVERSAL (Some (UNIVERSAL, size)) None) ;;
      withNewVar v addr k
    in (fix recur allocs :=
        match allocs with
          | nil => k
          | a::rest => doAlloc a (recur rest)
        end) allocs.

  Definition doMalloc {T} (size:nat) (succ:LLVM.var -> m (LLVM.label * T)) (fail:m LLVM.label) : m T :=
    base <- getBase ;;
    limit <- getLimit ;;
    baseCasted <- emitExp (LLVM.Ptrtoint_e PTR_TYPE (% base) UNIVERSAL) ;;
    limitCasted <- emitExp (LLVM.Ptrtoint_e PTR_TYPE (% limit) UNIVERSAL) ;;
    newBase <- emitExp (LLVM.Add_e true false UNIVERSAL (% baseCasted) (LLVM.Constant (LLVM.Int_c (Z_of_nat size)))) ;;
    newBaseCasted <- castTo PTR_TYPE (% newBase) ;;
    test <- emitExp (LLVM.Icmp_e LLVM.Ult UNIVERSAL (% newBase) (% limitCasted)) ;;
    labelSucc <- withBaseLimit newBaseCasted limit (succ base) ;;
    labelFail <- fail ;;
    emitInstr (LLVM.Br_cond_i (% test) (fst labelSucc) labelFail) ;;
    ret (snd labelSucc).

  Definition ERROR_LABEL : LLVM.var := "coq_error"%string.
  
  Definition exitLabel : m LLVM.label :=
    build <- get (MonadState := State_isExit) ;;
    match build with
      | None =>
        let m :=
          let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil LLVM.Void_t None (LLVM.Global ERROR_LABEL) nil (LLVM.Noreturn :: nil) in
          let instr := LLVM.Assign_i None call in
            emitInstr instr ;;
            emitInstr LLVM.Unreachable_i
            in
            l <- inFreshLabel m ;;
            put (Some (fst l)) ;;
            ret (fst l)
      | Some lbl => ret lbl
    end.

  Definition generateMalloc {T} (allocs : list (var * primtyp)) (k : m T) : m T :=
    let size := fold (fun alloc acc => let '(_,t) := alloc in acc + WORD_SIZE + sizeof t) 0 allocs in
    let doGeps base allocs k :=
      let doGep alloc k offset :=
        let '(v,t) := alloc in
        let size := WORD_SIZE + sizeof t in
        index <- opgen (Int_o (Z.of_nat (offset + 1))) ;;
        addr <- emitExp (LLVM.Getelementptr_e false PTR_TYPE base ((UNIVERSAL,index)::nil)) ;;
        withNewVar v addr (k (offset + size))
      in inFreshLabel ((fix recur allocs :=
        match allocs with
          | nil => (fun _ => k)
          | a::rest => doGep a (recur rest)
        end) allocs 0)
    in doMalloc size (fun base => doGeps (%base) allocs k) exitLabel.

  (* Should use primtyp at least as a check *)
  Definition generateLoad T (dest : var) (t : primtyp) (index : Z) (ptr : var) (k : m T) : m T :=
    ptr <- opgen (Var_o ptr) ;;
    index <- opgen (Int_o index) ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE ptr ((UNIVERSAL,index)::nil) in
    elem <- emitExp gep ;;
    load <- emitExp (LLVM.Load_e false false PTR_TYPE (%elem) None None None false) ;;
    withNewVar dest load k.

  (* Should use primtyp at least as a check *)
  Definition generateStore T (t : primtyp) (v : op) (index : Z) (ptr : var) (k : m T) : m T :=
    ptr <- opgen (Var_o ptr) ;;
    index <- opgen (Int_o index) ;;
    value <- opgen v ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE ptr ((UNIVERSAL,index)::nil) in
    elem <- emitExp gep ;;
    emitInstr (LLVM.Store_i false false UNIVERSAL value PTR_TYPE (%elem) None None false) ;;
    k.

  Definition generateInstr {T} (i : Low.instr) (k : m T) : m T :=
    match i with
      | Primop_i v p os =>
        generatePrim v p os k
      | Alloca_i allocs =>
        generateAlloca allocs k
      | Malloc_i allocs =>
        generateMalloc allocs k
      | Load_i d t i s =>
        generateLoad d t i s k
      | Store_i t v i d =>
        generateStore t v i d k
    end.

  Definition HALT_LABEL : LLVM.var := "coq_done"%string.

  Definition RET_TYPE arity :=
    LLVM.Struct_t false (PTR_TYPE::PTR_TYPE::(Low.count_to (fun _ => UNIVERSAL) arity)).

  Definition pgen (p : pattern) : m Z :=
      match p with
        | Int_p i => ret i
        | Con_p c =>
          c <- tagForConstructor c ;;
          ret c
      end.

  Definition generateCall (retVal : var) (fptr : op) (args : list op) (conts : list cont) : m unit :=
base <- getBase ;;
        limit <- getLimit ;;
        args <- mapM opgen args ;;
        let args := (PTR_TYPE, % base, nil) ::
                    (PTR_TYPE, % limit, nil) ::
                    map (fun x => (UNIVERSAL, x, nil)) args in
        f <- opgen fptr ;;
        (* XXX NEED TO DEAL WITH OTHER ARITIES OF CONSTRUCTORS? CAST TO APPROPRIATE FUN TYPE? *)
        let arity := 1 in
        match conts with
          | nil =>    
            let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil LLVM.Void_t None f args (LLVM.Noreturn :: nil) in
            let instr := LLVM.Assign_i None call in
            emitInstr instr ;;
            emitInstr LLVM.Unreachable_i
          | (inl 0)::nil =>
            (* XXX NEED TO DEAL WITH OTHER ARITIES OF CONSTRUCTORS? CAST TO APPROPRIATE FUN TYPE? *)
            let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil (RET_TYPE arity) None f args nil in
            result <- emitExp call ;;
            emitInstr (LLVM.Ret_i (Some (RET_TYPE arity,%result)))
          | (inr lbl)::nil =>
            let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil (RET_TYPE arity) None f args nil in
            result <- emitExp call ;;
            let extractResult type index :=
              index <- opgen (Int_o index) ;;
              let gep := LLVM.Getelementptr_e false (RET_TYPE arity) (%result) ((type,index)::nil) in
              elem <- emitExp gep ;;
              value <- emitExp (LLVM.Load_e false false type (%elem) None None None false) ;;
              ret value
            in
            newBase <- extractResult PTR_TYPE 0%Z ;;
            newLimit <- extractResult PTR_TYPE 1%Z ;;
            result <- extractResult UNIVERSAL 2%Z ;;
            (* Call the next continuation here *)
            withBaseLimit newBase newLimit (
              addJump lbl ((%result)::nil) ;;
              emitInstr (LLVM.Br_uncond_i lbl)
              )
          | _ => raise "Multiple continuations not supported yet"%string
        end.
    

  Definition generateTerm (t : Low.term) : m unit :=
    match t with
      | Halt_tm arg =>
        base <- getBase ;;
        limit <- getLimit ;;
        o <- opgen arg ;;
        let args := (PTR_TYPE, % base, nil) ::
                    (PTR_TYPE, % limit, nil) ::
                    (UNIVERSAL, o, nil) :: nil in
        let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil LLVM.Void_t None (LLVM.Global HALT_LABEL) args (LLVM.Noreturn :: nil) in
        let instr := LLVM.Assign_i None call in
        emitInstr instr ;;
        emitInstr LLVM.Unreachable_i
      | Call_tm retVal fptr args conts =>
        generateCall retVal fptr args conts
      | Cont_tm cont args =>
        match cont with
          | inl 0 =>
            let TYPE := RET_TYPE (length args) in
            base <- getBase ;;
            limit <- getLimit ;;
            retVal <- emitExp (LLVM.Insertvalue_e TYPE (LLVM.Constant LLVM.Undef_c) PTR_TYPE (%base) 0 nil) ;;
            retVal <- emitExp (LLVM.Insertvalue_e TYPE (%retVal) PTR_TYPE (%limit) 1 nil) ;;
            retVal <- (fix recur n args retVal :=
              match args with
                | nil =>
                  ret retVal
                | a::rest =>
                  arg <- opgen a ;;
                  retVal <- emitExp (LLVM.Insertvalue_e TYPE retVal UNIVERSAL arg n nil) ;;
                  recur (n+1) rest (%retVal)
              end) 2 args (%retVal) ;;
            emitInstr (LLVM.Ret_i (Some (TYPE,retVal)))
          | inl _ => raise "Multiple continuations not supported yet"%string
          | inr lbl =>
            newArgs <- mapM opgen args ;;
            addJump lbl newArgs ;;
            emitInstr (LLVM.Br_uncond_i lbl)
        end
      | Switch_tm op arms default => 
        v <- opgen op ;;
        arms <- mapM (fun pat =>
          let '(p,target,args) := pat in
            tag <- pgen p ;;
            inFreshLabel (
              args <- mapM opgen args ;;
              addJump target args ;;
              emitInstr (LLVM.Br_uncond_i target) ;;
              ret tag
            )) arms ;;
        default <- match default with
                     | None => 
                       v <- exitLabel ;;
                       ret (v,tt)
                     | Some (target,args) =>
                       inFreshLabel (
                         args <- mapM opgen args ;;
                         addJump target args ;;
                         emitInstr (LLVM.Br_uncond_i target) ;;
                         ret tt
                       )
                   end ;;
        let labels := map (fun x => (UNIVERSAL,snd x,fst x)) arms in
        emitInstr (LLVM.Switch_i UNIVERSAL v (fst default) labels)
    end.

  Definition generateBlock (l : label) (b : Low.block) : m unit :=
    let block :=
      (fix recur instrs :=
        match instrs with
          | nil => generateTerm (b_term b)
          | i::rest => generateInstr i (recur rest)
        end) (b_insns b) in
      withLabel l block.

  Definition genBlocks (blocks : alist label block) : m unit :=
    iterM (fun block => let '(l,b) := block in generateBlock l b) blocks.

End monadic.


Definition m : Type -> Type :=
    eitherT string (writerT (Monoid_CFG) (readerT (map_ctor Z) (readerT (LLVM.var * LLVM.var) (readerT (map_var lvar)
(stateT (option LLVM.label) (stateT (list LLVM.block) (stateT LLVM.block (state (nat * nat))))))
))).

Definition runM T (ctor_m : map_ctor Z) (var_m : map_var lvar) (cmd : m T) : string + (T  * CFG * list LLVM.block) :=
    let res := (runState (runStateT (runStateT (runStateT (runReaderT (runReaderT (runReaderT (runWriterT (unEitherT cmd)) ctor_m) ("base", "limit")%string) var_m) None) nil) (None, nil)) (0,0)) in
    match res with
      | (((((inl e, _), _), _), _), _) => inl e
      | (((((inr x, cfg), _), l), b), _) => inr (x, cfg, b :: l)
    end.

Definition runGenBlocks (ctor_m : map_ctor Z) (var_m : map_var lvar) (blocks : alist label block) : string + (unit * CFG * list LLVM.block) :=
  runM ctor_m var_m (genBlocks (m := m) blocks).

Definition generateFunction (ctor_m : map_ctor Z) (f : Low.function) : string + LLVM.topdecl :=
  let f_params : list (LLVM.type * LLVM.var * list LLVM.param_attr) := 
    Reducible.map (fun (x : Env.var) => (UNIVERSAL, runShow (show x) : string, nil : list LLVM.param_attr)) (f_args f) in
  (* should figure out return type *)
  let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil (runShow (show (f_name f))) f_params nil None None GC_NAME in 
  let locals : map_var lvar := fold_left (fun (acc : map_var lvar) v => 
    let lv : LLVM.var := runShow (show v) in Maps.add v lv acc) (f_args f) Maps.empty
  in  
  match runGenBlocks ctor_m locals (f_body f) with
    | inl e => inl e
    | inr (_,cfg,blocks) => inr (LLVM.Define_d header blocks) (* DO SOMETHING WITH CFG HERE *)
  end.
  
  Definition coq_error_decl := 
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_error"%string nil nil None None None in
      LLVM.Declare_d header.
  
  Definition coq_done_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_done"%string ((UNIVERSAL, "o", nil)::nil)%string nil None None None in
      LLVM.Declare_d header.

  Parameter generateProgram : forall (word_size : nat) (mctor : map_ctor Z) (p : Low.program), string + LLVM.module.
(*
    let decls := map generateFunction (p_topdecl p)
      in coq_error_decl :: coq_done_decl :: decls.
*)
End globals.
End maps.
End sized.
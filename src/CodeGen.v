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
  Context {FM_var : forall x, Foldable (map_var x) (var * x)}.
  Context {M_ctor : forall x, Foldable (map_ctor x) (constructor * x)}.
  Context {FM_ctor : DMap constructor map_ctor}.

  Context {DMap_blocks : DMap label (alist label)}.

  Variable map_lbl : Type -> Type.
  Context {Map_lbl : DMap label map_lbl}.
  Context {Foldable_lbl : forall a, Foldable (map_lbl a) (label * a)}.
  Definition CFG := map_lbl (lset (@eq (label * list LLVM.value))).
  Context {DS: DSet (lset (@eq (label * list LLVM.value))) (@eq (label * list LLVM.value))}.
  Definition Monoid_CFG : Monoid.Monoid CFG :=
    {| Monoid.monoid_plus := fun x y => Maps.combine (K := label) (fun k l r => union (R:=@eq (label * list LLVM.value)) l r) x y
     ; Monoid.monoid_unit := Maps.empty |}.    

Section globals.
  Variable globals : map_var (LLVM.value * LLVM.type).

Section monadic.
  Variable m : Type -> Type.
  Context {Monad : Monad m}.
  Context {Exception : MonadExc string m}.
  Context {State_fresh : MonadState (nat * nat) m}.
  Context {State_varmap : MonadState (map_var lvar) m}.
  Context {Reader_ctormap : MonadReader (map_ctor Z) m}.
  Context {Reader_baselimit : MonadReader (LLVM.var * LLVM.var) m}.
  Context {State_instrs : MonadState (LLVM.block) m}.
  Context {State_blks : MonadState (list LLVM.block) m}.
  Context {State_isExit : MonadState (option LLVM.label) m}.
  Context {Writer_cfg : MonadWriter Monoid_CFG m}.
  Context {State_trace : MonadState (list string) m}.

  Definition trace (s : string) : m unit :=
    ls <- get (MonadState := State_trace) ;;
    put (MonadState := State_trace) (s::ls).

  Definition freshVar (v : Env.var) : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
      put (S v_n, l_n) ;;
      ret (runShow (show v) (nat2string10 v_n))%string.     

  Definition freshLLVMVar (s : string) : m LLVM.var :=
    freshVar (wrapVar s).

  Definition freshLabel : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
      put (v_n, S l_n) ;;
      ret ("lbl" ++ nat2string10 l_n)%string.
  
  Definition withNewVar (cps : Env.var) (llvm : LLVM.var) : m unit :=
    modify (Maps.add cps llvm) ;; ret tt.
  
  Definition emitInstr (i : LLVM.instr) : m unit :=
    st <- get (MonadState := State_instrs) ;;
    let '(blbl, binstrs) := st in
      put (blbl, binstrs ++ i :: nil).

  Definition comment (s : string) : m unit :=
    emitInstr (LLVM.Comment_i s).

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

  Definition getBase : m LLVM.var :=
    x <- ask (MonadReader := Reader_baselimit) ;;
    ret (fst x).

  Definition getLimit : m LLVM.var :=
    x <- ask (MonadReader := Reader_baselimit) ;;
    ret (snd x).

  Definition withBaseLimit {T} (base limit : LLVM.var) : m T -> m T :=                                                              
    local (MonadReader := Reader_baselimit) (fun _ => (base,limit)). 

  Definition addJump (to : label) (args : list LLVM.value) : m unit :=
    from <- getLabel ;;
    base <- getBase ;;
    limit <- getLimit ;;
    tell (Maps.singleton to ((from,(%base)::(%limit)::args) :: nil)).

  Definition tagForConstructor (c : constructor) : m Z :=
    x <- ask (MonadReader := Reader_ctormap) ;;
    match Maps.lookup c x with
      | None => raise ("error looking for '" ++ c ++ "' in {" ++ (to_string x) ++ "}")%string
      | Some z => ret z
    end.
  
  Definition emitExp (v : LLVM.var) (e : LLVM.exp) : m unit :=
    emitInstr (LLVM.Assign_i (Some (LLVM.Local v)) e).

  Definition emitExpFresh (e : LLVM.exp) : m LLVM.var :=
    x <- freshVar (Env.Named_v "_"%string None) ;;
    emitInstr (LLVM.Assign_i (Some (LLVM.Local x)) e) ;;
    ret x.
  
  Definition castTo (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    x <- freshVar (Env.Named_v "_"%string None) ;;
    match ty with
      | LLVM.Pointer_t _ _ => 
        emitExp x (LLVM.Inttoptr_e UNIVERSAL v ty)
      | _ => 
        emitExp x (LLVM.Bitcast_e UNIVERSAL v ty)
    end ;;
    ret x.
  
  Definition castFrom (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    x <- freshVar (Env.Named_v "_"%string None) ;;
    match ty with
      | LLVM.Pointer_t _ _ =>
        emitExp x (LLVM.Ptrtoint_e ty v UNIVERSAL)
      | _ =>
        emitExp x (LLVM.Bitcast_e ty v UNIVERSAL)
    end ;;
    ret x.

  Definition opgen (op : op) : m LLVM.value :=
    match op with
      | Var_o v => 
        x <- gets (Maps.lookup v) ;;
        match x with
          | None => 
            match Maps.lookup v globals with
              | None =>
                v' <- freshVar v ;;
                withNewVar v v' ;;
                ret (LLVM.Local v')
              | Some (v,t) => 
                asLocal <- castFrom t v ;;
                ret (%asLocal)
            end
          | Some v => ret (LLVM.Local v)
        end
      | Con_o c => 
        z <- tagForConstructor c ;;
        ret (LLVM.Constant (LLVM.Int_c z))
      | Int_o i => ret (LLVM.Constant (LLVM.Int_c i))
      | InitWorld_o => raise "BUG: Got initial world. should have been erased"
    end%string.

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

    Definition forLocal (x : Env.var) : m LLVM.var :=
      x' <- opgen (Var_o x) ;;
      match x' with
        | LLVM.Local v => ret v 
        | _ => raise "BUG"%string
      end.


  Definition generatePrim (x : Env.var) (p : Low.primop) (os : list op) : m unit :=
    x' <- forLocal x ;;
    match p with
      | Eq_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Icmp_e LLVM.Eq UNIVERSAL l r)
      | Neq_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Icmp_e LLVM.Ne UNIVERSAL l r)
      | Lt_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Icmp_e LLVM.Slt UNIVERSAL l r) (** Signed? **)
      | Lte_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Icmp_e LLVM.Sle UNIVERSAL l r) (** Signed? **)
          
      | Plus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Add_e false false UNIVERSAL l r )
      | Minus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Sub_e false false UNIVERSAL l r )
      | Times_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        emitExp x' (LLVM.Mul_e false false UNIVERSAL l r )

      | Ptr_p => (* XXX Should use Select instruction *)
        p <- opgen_list1 os ;;
        y <- emitExpFresh (LLVM.And_e UNIVERSAL p (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExpFresh (LLVM.Icmp_e LLVM.Ne UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExpFresh (LLVM.Zext_e (LLVM.I_t 1) (%y) UNIVERSAL) ;;
        y <- emitExpFresh (LLVM.Shl_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        emitExp x' (LLVM.Add_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z))
    end.

  Definition generateMop T (x : Env.var) (p : Low.mop) (os : list op) (k : m T) : m T :=
    match p with
      | PrintInt_m => k (* XXX IMPLEMENT! *)
    end.

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
      addr <- forLocal v ;;
      emitExp addr (LLVM.Alloca_e UNIVERSAL (Some (UNIVERSAL, size)) None) ;;
      k
    in (fix recur allocs :=
        match allocs with
          | nil => k
          | a::rest => doAlloc a (recur rest)
        end) allocs.

  Definition doMalloc {T} (size:nat) (succ:LLVM.var -> m (LLVM.label * T)) (fail:m LLVM.label) : m T :=
    base <- getBase ;;
    limit <- getLimit ;;
    baseCasted <- emitExpFresh (LLVM.Ptrtoint_e PTR_TYPE (% base) UNIVERSAL) ;;
    limitCasted <- emitExpFresh (LLVM.Ptrtoint_e PTR_TYPE (% limit) UNIVERSAL) ;;
    newBase <- emitExpFresh (LLVM.Add_e true false UNIVERSAL (% baseCasted) (LLVM.Constant (LLVM.Int_c (Z_of_nat size)))) ;;
    newBaseCasted <- castTo PTR_TYPE (% newBase) ;;
    test <- emitExpFresh (LLVM.Icmp_e LLVM.Ult UNIVERSAL (% newBase) (% limitCasted)) ;;
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
        let size := sizeof t in
        len <- opgen (Int_o (Z.of_nat size)) ;;
        begin <- opgen (Int_o (Z.of_nat offset)) ;;
        comment "Get a pointer to the header of the object" ;;
        hdr <- emitExpFresh (LLVM.Getelementptr_e false PTR_TYPE base ((UNIVERSAL,begin)::nil)) ;;
        comment "Initialize the header with the size of the object" ;;
        emitInstr (LLVM.Store_i false false UNIVERSAL len PTR_TYPE (%hdr) None None false) ;;
        index <- opgen (Int_o (Z.of_nat 1)) ;;
        comment "Get a pointer to the start of the object" ;;
        addr <- forLocal v ;;
        emitExp addr (LLVM.Getelementptr_e false PTR_TYPE (%hdr) ((UNIVERSAL,index)::nil)) ;;
        k (offset + size + 1)
      in inFreshLabel ((fix recur allocs :=
        match allocs with
          | nil => (fun _ => k)
          | a::rest => doGep a (recur rest)
        end) allocs 0)
    in doMalloc size (fun base => doGeps (%base) allocs k) exitLabel.

  (* Should use primtyp at least as a check *)
  Definition generateLoad T (dest : var) (t : primtyp) (index : Z) (ptr : op) (k : m T) : m T :=
    ptr <- opgen ptr ;;
    index <- opgen (Int_o index) ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE ptr ((UNIVERSAL,index)::nil) in
    elem <- emitExpFresh gep ;;
    load <- forLocal dest ;;
    emitExp load (LLVM.Load_e false false PTR_TYPE (%elem) None None None false) ;;
    k.

  (* Should use primtyp at least as a check *)
  Definition generateStore T (t : primtyp) (v : op) (index : Z) (ptr : op) (k : m T) : m T :=
    ptr <- opgen ptr ;;
    index <- opgen (Int_o index) ;;
    value <- opgen v ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE ptr ((UNIVERSAL,index)::nil) in
    elem <- emitExpFresh gep ;;
    emitInstr (LLVM.Store_i false false UNIVERSAL value PTR_TYPE (%elem) None None false) ;;
    k.

  Definition generateInstr {T} (i : Low.instr) (k : m T) : m T :=
    match i with
      | Primop_i v p os =>
        generatePrim v p os ;; k
      | Alloca_i allocs =>
        generateAlloca allocs k
      | Malloc_i allocs =>
        generateMalloc allocs k
      | Load_i d t i s =>
        generateLoad d t i s k
      | Store_i t v i d =>
        generateStore t v i d k
      | Bind_i v m os =>
        generateMop v m os k
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
        result <- emitExpFresh call ;;
        emitInstr (LLVM.Ret_i (Some (RET_TYPE arity,%result)))
      | (inr lbl)::nil =>
        let call := LLVM.Call_e true (Some LLVM.Fast_cc) nil (RET_TYPE arity) None f args nil in
        result <- emitExpFresh call ;;
        let extractResult type index :=
          index <- opgen (Int_o index) ;;
          let gep := LLVM.Getelementptr_e false (RET_TYPE arity) (%result) ((type,index)::nil) in
          elem <- emitExpFresh gep ;;
          value <- emitExpFresh (LLVM.Load_e false false type (%elem) None None None false) ;;
          ret value
        in
        newBase <- extractResult PTR_TYPE 0%Z ;;
        newLimit <- extractResult PTR_TYPE 1%Z ;;
        result <- extractResult UNIVERSAL 2%Z ;;
        (* Call the next continuation here *)
        withBaseLimit newBase newLimit (
          from <- getLabel ;;
          trace ("generateCall: addJump to " ++ lbl ++ " from " ++ from) ;;
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
            retVal <- emitExpFresh (LLVM.Insertvalue_e TYPE (LLVM.Constant LLVM.Undef_c) PTR_TYPE (%base) 0 nil) ;;
            retVal <- emitExpFresh (LLVM.Insertvalue_e TYPE (%retVal) PTR_TYPE (%limit) 1 nil) ;;
            retVal <- (fix recur n args retVal :=
              match args with
                | nil =>
                  ret retVal
                | a::rest =>
                  arg <- opgen a ;;
                  retVal <- emitExpFresh (LLVM.Insertvalue_e TYPE retVal UNIVERSAL arg n nil) ;;
                  recur (n+1) rest (%retVal)
              end) 2 args (%retVal) ;;
            emitInstr (LLVM.Ret_i (Some (TYPE,retVal)))
          | inl _ => raise "Multiple continuations not supported yet"%string
          | inr lbl =>
            newArgs <- mapM opgen args ;;
            from <- getLabel ;;
            trace ("Cont_tm: addJump to " ++ lbl ++ " from " ++ from) ;;
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
              from <- getLabel ;;
              trace ("Switch_tm: addJump to " ++ target ++ " from " ++ from) ;;
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
                         from <- getLabel ;;
                         trace ("Switch_tm default: addJump to " ++ target ++ " from " ++ from) ;;
                         addJump target args ;;
                         emitInstr (LLVM.Br_uncond_i target) ;;
                         ret tt
                       )
                   end ;;
        let labels := map (fun x => (UNIVERSAL,snd x,fst x)) arms in
        emitInstr (LLVM.Switch_i UNIVERSAL v (fst default) labels)
    end.

  Definition generateInstructions (b : Low.block) : m unit :=
    (fix recur instrs :=
      match instrs with
        | nil => generateTerm (b_term b)
        | i::rest => generateInstr i (recur rest)
      end) (b_insns b).

  Definition generateEntry (b : Low.block) : m unit :=
    match length (b_args b) with
      | 0 =>
        newBase <- ret "base"%string ;;
        newLimit <- ret "limit"%string ;;
        withBaseLimit newBase newLimit (generateInstructions b)
      | _ => raise "Entry block should take no arguments."%string
    end.

  Definition generateBlock (l : label) (b : Low.block) : m (label * list LLVM.var) :=
   let args := b_args b in
   newVars <- mapM freshVar args ;;
   newBase <- freshLLVMVar "base"%string ;;
   newLimit <- freshLLVMVar "limit"%string ;;
   withLabel l (
     withBaseLimit newBase newLimit (
       generateInstructions b
     )
   ) ;;
   ret (l,newBase::newLimit::newVars).

  Definition genBlocks (entryLbl : label) (blocks : alist label block) : m (list (label * list LLVM.var)) :=
    match lookup entryLbl blocks with
      | None => raise "Entry block not found"%string
      | Some entryBlock =>
        entry <- generateEntry entryBlock ;;
        let nonEntry := Maps.filter _ (fun l _ => negb (eq_dec l entryLbl)) blocks in
        mapM (fun block => let '(l,b) := block in generateBlock l b) nonEntry
    end.

End monadic.

Definition m : Type -> Type :=
    eitherT string (writerT (Monoid_CFG) (readerT (map_ctor Z) (readerT (LLVM.var * LLVM.var) (stateT (map_var lvar)
(stateT (option LLVM.label) (stateT (list LLVM.block) (stateT LLVM.block (stateT (nat * nat) (state (list string)))))))
))).

Definition runM T (ctor_m : map_ctor Z) (var_m : map_var lvar) (cmd : m T) : (string * list string) + (T  * CFG * list LLVM.block * list string) :=
    let res := (runState (runStateT (runStateT (runStateT (runStateT (evalStateT (runReaderT (runReaderT (runWriterT (unEitherT cmd)) ctor_m) ("base", "limit")%string) var_m) None) nil) (None, nil)) (0,0)) nil) in
    match res with
      | ((((((inl e, _), _), _), _), _), t) => inl (e,t)
      | ((((((inr x, cfg), _), l), b), _), t) => inr (x, cfg, b :: l,t)
    end.

Definition runGenBlocks (ctor_m : map_ctor Z) (var_m : map_var lvar) (entry : label) (blocks : alist label block) : (string * list string) + ((list (label * list LLVM.var)) * CFG * list LLVM.block * list string) :=
  runM ctor_m var_m (genBlocks (m := m) entry blocks).

Fixpoint combine_with {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : option (list C) :=
  match l,l' with
    | x::tl, y::tl' =>
      let h := f x y in
      t <- combine_with f tl tl' ;;
      ret (h::t)
    | nil, nil =>
      ret nil
    | _, _ =>
      None
  end.

Definition generatePhi (v : LLVM.var) (vs : list (LLVM.value * label)) : LLVM.instr :=
  LLVM.Assign_i (Some (%v)) (LLVM.Phi_e UNIVERSAL vs).

Definition rewriteBlock (cfg : CFG) (formals : alist label (list LLVM.var)) (block : LLVM.block) : string + LLVM.block.
refine (
  match block with
    | (None,_) => ret block
    | (Some lbl,intrs) =>
      match lookup lbl cfg with
        | None => ret block
        | Some callers =>
          let reassoc := List.map (fun c => let '(caller,args) := c in List.map (fun a => (a,caller)) args) callers in
          let phi_args :=
            match reassoc with
              | nil => ret nil
              | h::nil => ret (map (fun e => e::nil) h)
              | h::rest => foldM (fun elem acc => combine_with (fun e a => e::a) elem acc) (map (fun e => e::nil) h) rest
            end in
          match phi_args with
            | Some args =>
              match lookup lbl formals with
                | Some formals =>
                  match combine_with (fun f a => (f,a)) formals args with
                    | Some phi_recs =>
                      let phis := map (fun e => let '(f,a) := e in generatePhi f a) phi_recs in
                        ret (Some lbl,phis ++ intrs)
                    | _ => raise ("Control-flow graph inconsisent with Low.function: wrong number of args\n" ++
                                  "block: " ++ (to_string lbl) ++ " " ++
                                  "formals: " ++ (to_string formals) ++ " " ++
                                  "args: " ++ (to_string args) ++ " "
                                 )%string
                  end
                | _ => raise "Inconsistent formal counts"%string
              end
            | _ => raise "Inconsistent phi node argument counts"%string
          end
      end
  end).
Defined.

Definition generateFunction (ctor_m : map_ctor Z) (f : Low.function) : (string * list string) + LLVM.topdecl :=
  let f_params : list (LLVM.type * LLVM.var * list LLVM.param_attr) := 
    let formals :=
      Reducible.map (fun (x : Env.var) => (UNIVERSAL, runShow (show x) : string, nil : list LLVM.param_attr)) (f_args f) in
    (PTR_TYPE,"base"%string,nil)::(PTR_TYPE,"limit"%string,nil)::formals in
  (* right return type always? *)
  let type := RET_TYPE 1 in
  let header := LLVM.Build_fn_header None None CALLING_CONV false type nil (runShow (show (f_name f))) f_params nil None None GC_NAME in 
  let locals : map_var lvar := fold_left (fun (acc : map_var lvar) v => 
    let lv : LLVM.var := runShow (show v) in Maps.add v lv acc) (f_args f) Maps.empty
  in  
  match runGenBlocks ctor_m locals (f_entry f) (f_body f) with
    | inl e => inl e
    | inr (formals,cfg,blocks,t) =>
      let addPhis :=
        finalBlocks <- mapM (rewriteBlock cfg formals) blocks ;;
        ret (LLVM.Define_d header finalBlocks) in
      match addPhis with
        | inl e => inl (e,t)
        | inr p => inr p
      end
  end.

End globals.

  Definition generateGlobals (fs : list Low.function) : map_var (LLVM.value * LLVM.type) :=
    fold (fun f map =>
      let fname := f_name f in
      let argTypes := PTR_TYPE::PTR_TYPE::(Low.count_to (fun _ => UNIVERSAL) (length (f_args f))) in
      let type := LLVM.Pointer_t ADDR_SPACE (LLVM.Fn_t (RET_TYPE 1) argTypes false) in
      Maps.add fname (LLVM.Global (runShow (show fname)),type) map) Maps.empty fs.

  Definition coq_error_decl := 
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_error"%string nil nil None None None in
      LLVM.Declare_d header.
  
  Definition coq_done_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_done"%string ((UNIVERSAL, "o", nil)::nil)%string nil None None None in
      LLVM.Declare_d header.

End maps.

End sized.

Section program.
Variable map_ctor : Type -> Type.
Context {M_ctor : forall x, Foldable (map_ctor x) (constructor * x)}.
Context {FM_ctor : DMap constructor map_ctor}.

(* XXX Need to resolve the missing context DSet (lset (@eq (label * list LLVM.value))) (@eq (label * list LLVM.value)) *)

Definition generateProgram (word_size : nat) (mctor : map_ctor Z) (p : Low.program) : string + LLVM.module :=
  let globals := generateGlobals (FM := DMap_alist RelDec_var_eq) word_size (p_topdecl p) in
  let program := 
    decls <- mapM (M := Monad_either (string * list string)) (generateFunction word_size globals mctor) (p_topdecl p) ;;
    ret (coq_error_decl :: coq_done_decl word_size :: decls) 
  in
  match program with
    | inl (e,t) => inl (e ++ "  " ++ to_string t)%string
    | inr p => inr p
  end.

End program.

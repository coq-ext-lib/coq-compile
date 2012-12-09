Require Import CoqCompile.Low.
Require Import CoqCompile.LLVM.
Require Import CoqCompile.TraceMonad.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Data.Char.
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

  Definition CALLING_CONV : option LLVM.cconv := None.
  Definition GC_NAME : option string := Some "shadow-stack"%string.

  Definition ALLOC_FN : string := "coq_alloc"%string.
  Definition PRINTCHAR_FN : string := "coq_printchar"%string.
  Definition GCROOT := "llvm.gcroot"%string.

  Definition PTR_TYPE := LLVM.Pointer_t ADDR_SPACE UNIVERSAL.
  Definition PTR_PTR_TYPE := LLVM.Pointer_t ADDR_SPACE PTR_TYPE.
  Definition BUMP_TYPE := LLVM.Struct_t false (PTR_TYPE::PTR_TYPE::nil).
  Definition ALLOC_TYPE := LLVM.Struct_t false (BUMP_TYPE::PTR_TYPE::nil).
  Definition CHAR_PTR := LLVM.Pointer_t ADDR_SPACE (LLVM.I_t 8).
  Definition CHAR_PTR_PTR := LLVM.Pointer_t ADDR_SPACE CHAR_PTR.

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
  Context {DS_cfg : DSet (lset (@eq (label * list LLVM.value))) (@eq (label * list LLVM.value))}.
  Definition CFG := map_lbl (lset (@eq (label * list LLVM.value))).
  Definition Monoid_CFG : Monoid.Monoid CFG :=
    {| Monoid.monoid_plus := fun x y => Maps.combine (K := label) (fun k l r => union l r) x y
     ; Monoid.monoid_unit := Maps.empty |}.    

Section globals.
  Variable globals : map_var (LLVM.value * LLVM.type).

Section monadic.
  Variable m : Type -> Type.
  Context {Monad : Monad m}.
  Context {Exception : MonadExc string m}.
  Context {State_fresh : MonadState (nat * nat) m}.
  Context {Reader_varmap : MonadReader (map_var LLVM.value) m}.
  Context {Reader_ctormap : MonadReader (map_ctor Z) m}.
  Context {Reader_bumpptrs : MonadReader LLVM.var m}.
  Context {State_instrs : MonadState (LLVM.block) m}.
  Context {State_blks : MonadState (list LLVM.block) m}.
  Context {State_isExit : MonadState (option LLVM.label) m}.
  Context {State_gcroots : MonadState (list (Env.var * LLVM.var)) m}.
  Context {Writer_cfg : MonadWriter Monoid_CFG m}.
  Context {Trace : MonadTrace string m}.

  Definition trace (s : string) : m unit :=
    mlog s.

  Definition cleanString (s : string) : string :=
    map (fun c => if eq_dec c "~"%char then "_"%char else c) s.

  Definition cleanVar (v : Env.var) : Env.var :=
    match v with
      | Anon_v _ => v
      | Named_v s p => Named_v (cleanString s) p
    end.

  Definition freshVar (v : Env.var) : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
    put (S v_n, l_n) ;;
    let v := cleanVar v in
    ret (runShow (cat (show v) (show v_n))).

  Definition freshLLVMVar (s : string) : m LLVM.var :=
    freshVar (wrapVar s).

  Definition freshLabel : m LLVM.var :=
    x <- get ;;
    let '(v_n, l_n) := x in 
      put (v_n, S l_n) ;;
      ret ("lbl" ++ nat2string10 l_n)%string.
  
  Definition withNewValue {T} (cps : Env.var) (llvm : LLVM.value) : m T -> m T :=
    local (MonadReader := Reader_varmap) (Maps.add cps llvm).
  
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

  Definition inEntryBlock {T} (c : m T) : m T :=
    st <- get (MonadState := State_instrs) ;;
    put (None,nil) ;;
    t <- c ;;
    new <- get (MonadState := State_instrs) ;;
    let '(lbl,rest) := st in
    let '(_,new) := new in
    put (lbl,new++rest) ;;
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

  Definition getBumpPtrs : m LLVM.var :=
    x <- ask (MonadReader := Reader_bumpptrs) ;;
    ret x.

  Definition withBumpPtrs {T} (ptrs : LLVM.var) : m T -> m T :=                                                              
    local (MonadReader := Reader_bumpptrs) (fun _ => ptrs). 

  Definition addJump (to : label) (args : list LLVM.value) : m unit :=
    from <- getLabel ;;
    ptrs <- getBumpPtrs ;;
    tell (Maps.singleton to ((from,(%ptrs)::args) :: nil)).

  Definition tagForConstructor (c : constructor) : m Z :=
    x <- ask (MonadReader := Reader_ctormap) ;;
    match Maps.lookup c x with
      | None => raise ("error looking for '" ++ c ++ "' in {" ++ (to_string x) ++ "}")%string
      | Some z => ret z
    end.
  
  Definition emitExp (e : LLVM.exp) : m LLVM.var :=
    x <- freshVar (Env.Named_v "_"%string None) ;;
    emitInstr (LLVM.Assign_i (Some (LLVM.Local x)) e) ;;
    ret x.
  
  Definition castTo (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    match ty with
      | LLVM.Pointer_t _ _ => 
        emitExp (LLVM.Inttoptr_e UNIVERSAL v ty)
      | _ => 
        emitExp (LLVM.Bitcast_e UNIVERSAL v ty)
    end.

  Definition castFrom (ty : LLVM.type) (v : LLVM.value) : m LLVM.var :=
    match ty with
      | LLVM.Pointer_t _ _ =>
        emitExp (LLVM.Ptrtoint_e ty v UNIVERSAL)
      | _ =>
        emitExp (LLVM.Bitcast_e ty v UNIVERSAL)
    end.

  Definition live (var : Env.var) : m bool :=
    x <- ask ;;
    match Maps.lookup var x with
      | None => ret false
      | Some _ => ret true
    end.

  Definition opgen (op : op) : m LLVM.value :=
    match op with
      | Var_o v => 
        x <- ask ;;
        match Maps.lookup v x with
          | None => 
            match Maps.lookup v globals with
              | None => raise ("Couldn't find variable '" ++ (to_string v) ++ "' in context: {"
                        ++ (to_string x) ++ "} or globals map: {" ++ (to_string globals) ++ "}")
              | Some (v,t) => 
                asLocal <- castFrom t v ;;
                ret (%asLocal)
            end
          | Some v => ret v
        end
      | Con_o c => 
        z <- tagForConstructor c ;;
        ret (LLVM.Constant (LLVM.Int_c z))
      | Int_o i => ret (LLVM.Constant (LLVM.Int_c i))
      | InitWorld_o => ret (LLVM.Constant (LLVM.Int_c 3)) (*raise "BUG: Got initial world. should have been erased"*)
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

  Definition reportUniversal (v : LLVM.value) : m unit :=
    let args := (UNIVERSAL,v,nil)::nil in
    let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global "coq_report"%string) args nil in
    emitInstr (LLVM.Assign_i None call).

  Definition reportPointer (v : LLVM.value) : m unit :=
    v <- castFrom PTR_TYPE v ;;
    let args := (UNIVERSAL,(%v),nil)::nil in
    let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global "coq_report"%string) args nil in
    emitInstr (LLVM.Assign_i None call).

  Definition addRoot (root : Env.var): m unit :=
    roots <- get (MonadState := State_gcroots) ;;
    var <- opgen (Var_o root) ;;
    rootVar <- freshLLVMVar (to_string root ++ "_root")%string ;;
    put (MonadState := State_gcroots) ((root,rootVar)::roots).

  Definition getRoots : m (list (Env.var * LLVM.var)) :=
    get (MonadState := State_gcroots).

  Definition storeRoots : m unit :=
    roots <- get (MonadState := State_gcroots) ;;
    iterM (fun root =>
      let '(v,r) := root in
      isLive <- live v ;;
      if isLive
        then
          var <- opgen (Var_o v) ;;
          var <- castTo PTR_TYPE var ;;
          emitInstr (LLVM.Store_i false true PTR_TYPE (%var) PTR_PTR_TYPE (%r) None None false)
        else
          emitInstr (LLVM.Store_i false true PTR_TYPE (LLVM.Constant LLVM.Null_c) PTR_PTR_TYPE (%r) None None false)) roots.

  Definition reloadRoots {T} (k : m T) : m T :=
    roots <- get (MonadState := State_gcroots) ;;
    (fix recur roots :=
      match roots with
        | nil => k
        | root::roots =>
          let '(v,r) := root in
          isLive <- live v ;;
          if isLive
            then
              ptr <- emitExp (LLVM.Load_e false true PTR_PTR_TYPE (%r) None None None false) ;;
              x <- castFrom PTR_TYPE (%ptr) ;;
              emitInstr (LLVM.Store_i false true PTR_TYPE (LLVM.Constant LLVM.Null_c) PTR_PTR_TYPE (%r) None None false) ;;
              withNewValue v (%x) (recur roots)
            else
              recur roots
      end) roots.

  Definition generatePrim {T} (x : Env.var) (p : Low.primop) (os : list op) (k : m T) : m T :=
    match p with
      | Eq_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Eq UNIVERSAL l r) ;;
        withNewValue x (%y) k
      | Neq_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL l r) ;;
        withNewValue x (%y) k
      | Lt_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Slt UNIVERSAL l r) ;; (** Signed? **)
        withNewValue x (%y) k
      | Lte_p =>
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Icmp_e LLVM.Sle UNIVERSAL l r) ;; (** Signed? **)
        withNewValue x (%y) k
          
      | Plus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Add_e false false UNIVERSAL l r ) ;;
        withNewValue x (%y) k
      | Minus_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Sub_e false false UNIVERSAL l r ) ;;
        withNewValue x (%y) k
      | Times_p => 
        lr <- opgen_list2 os ;;
        let '(l,r) := lr in
        y <- emitExp (LLVM.Mul_e false false UNIVERSAL l r ) ;;
        withNewValue x (%y) k

      | Ptr_p => (* XXX Should use Select instruction *)
        p <- opgen_list1 os ;;
        y <- emitExp (LLVM.And_e UNIVERSAL p (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Zext_e (LLVM.I_t 1) (%y) UNIVERSAL) ;;
        y <- emitExp (LLVM.Shl_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        y <- emitExp (LLVM.Add_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
        withNewValue x (%y) k
    end.

  Definition generateMop T (x : Env.var) (p : Low.mop) (os : list op) (k : m T) : m T :=
    match p with
      | PrintInt_m => 
        mlog "TODO: generate code for PrintInt"%string ;;
        k
      | PrintChar_m =>
        mlog "generating code for PrintChar"%string ;;
        match os with
          | arg::nil =>
            arg <- opgen arg ;;
            ptr <- castTo PTR_TYPE arg ;;
            let args := (PTR_TYPE,(%ptr),nil)::nil in
            let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global PRINTCHAR_FN) args nil in
            emitInstr (LLVM.Assign_i None call) ;;
            withNewValue x (LLVM.Constant (LLVM.Int_c 3)) k
          | _ => raise "PrintChar expects a single argument"%string
        end
    end.

  Fixpoint sizeof (t : primtyp) : nat :=
    match t with
      | Struct_t ts =>
        fold (fun t a => a + sizeof t) 0 ts
      | _ => 1
    end.

  Definition generateAlloca T (allocs : list (var * primtyp)) (k : m T) : m T :=
    let doAlloc alloc k :=
      let '(v,t) := alloc in
      match sizeof t with
        | 0 => k
        | n =>
          let size := n + 1 in
          addr <- emitExp (LLVM.Alloca_e UNIVERSAL (Some (UNIVERSAL, size)) None) ;;
          withNewValue v (%addr) k
      end
    in (fix recur allocs :=
        match allocs with
          | nil => k
          | a::rest => doAlloc a (recur rest)
        end) allocs.

  Definition doMalloc {T} (size:nat) (k : LLVM.var -> m T) : m T :=
    bumpptrs <- getBumpPtrs ;;
    size <- opgen (Int_o (Z.of_nat size));
    let args := (BUMP_TYPE,(%bumpptrs),nil)::(UNIVERSAL,size,nil)::nil in
    let call := LLVM.Call_e true CALLING_CONV nil ALLOC_TYPE None (LLVM.Global ALLOC_FN) args nil in
    storeRoots ;;
    retval <- emitExp call ;;
    reloadRoots (
      bumpptrs <- emitExp (LLVM.Extractvalue_e ALLOC_TYPE (%retval) 0 nil) ;;
      alloc <- emitExp (LLVM.Extractvalue_e ALLOC_TYPE (%retval) 1 nil) ;;
      withBumpPtrs bumpptrs (k alloc)
    ).
  
  Definition generateMalloc {T} (allocs : list (var * primtyp)) (k : m T) : m T :=
    let size := fold (fun alloc acc =>
      let '(_,t) := alloc in 
      match sizeof t with
        | 0 => acc
        | n => acc + 1 + n
      end) 0 allocs in
    let doGeps base allocs k :=
      let doGep alloc k offset :=
        let '(v,t) := alloc in
        let size := sizeof t in
        match size with
          | 0 => 
            comment ("Don't allocate empty tuples")%string ;;
            x <- castFrom PTR_TYPE (LLVM.Constant LLVM.Null_c) ;;
            withNewValue v (%x) (k offset)
          | size =>
            len <- opgen (Int_o (Z.of_nat size)) ;;
            begin <- opgen (Int_o (Z.of_nat offset)) ;;
            comment ("Allocating a tuple of size " ++ to_string len)%string ;;
            comment ("At offset " ++ (to_string offset) ++ " of allocation")%string ;;
            comment ("Get a pointer to the header")%string ;;
            hdr <- emitExp (LLVM.Getelementptr_e false PTR_TYPE base ((UNIVERSAL,begin)::nil)) ;;
            comment ("Store the tuple size")%string ;;
            emitInstr (LLVM.Store_i false false UNIVERSAL len PTR_TYPE (%hdr) None None false) ;;
            index <- opgen (Int_o (Z.of_nat 1)) ;;
            comment ("Get a pointer to the start of the object") ;;
            addr <- emitExp (LLVM.Getelementptr_e false PTR_TYPE (%hdr) ((UNIVERSAL,index)::nil)) ;;
            x <- castFrom PTR_TYPE (%addr) ;;
            comment ("Initialize the GC root") ;;
            withNewValue v (%x) (
              addRoot v ;;
              k (offset + size + 1)
            )
        end
      in (fix recur allocs :=
        match allocs with
          | nil => (fun _ => k)
          | a::rest => doGep a (recur rest)
        end) allocs 0
    in doMalloc size (fun base => doGeps (%base) allocs k).

  (* Should use primtyp at least as a check *)
  Definition generateLoad T (dest : var) (t : primtyp) (index : Z) (ptr : op) (k : m T) : m T :=
    ptr <- opgen ptr ;;
    idx <- opgen (Int_o index) ;;
    ptr <- castTo PTR_TYPE ptr ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE (%ptr) ((UNIVERSAL,idx)::nil) in
    elem <- emitExp gep ;;
    load <- emitExp (LLVM.Load_e false false PTR_TYPE (%elem) None None None false) ;;
    withNewValue dest (%load) (
      addRoot dest ;;
      k
    ).

  (* Should use primtyp at least as a check *)
  Definition generateStore T (t : primtyp) (v : op) (index : Z) (ptr : op) (k : m T) : m T :=
    ptr <- opgen ptr ;;
    idx <- opgen (Int_o index) ;;
    value <- opgen v ;;
    ptr <- castTo PTR_TYPE ptr ;;
    let gep := LLVM.Getelementptr_e false PTR_TYPE (%ptr) ((UNIVERSAL,idx)::nil) in      
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
      | Bind_i v m os =>
        generateMop v m os k
    end.

  Definition HALT_LABEL : LLVM.var := "coq_done"%string.

  Definition RET_TYPE arity :=
    LLVM.Struct_t false (BUMP_TYPE::(Low.count_to (fun _ => UNIVERSAL) arity)).

  Definition pgen (p : pattern) : m Z :=
      match p with
        | Int_p i => ret i
        | Con_p c =>
          c <- tagForConstructor c ;;
          ret c
      end.

  Definition computeFunctionType (arity : nat) : LLVM.type :=
    let argTypes := BUMP_TYPE::(Low.count_to (fun _ => UNIVERSAL) arity) in
    LLVM.Pointer_t ADDR_SPACE (LLVM.Fn_t (RET_TYPE 1) argTypes false).

  Definition generateBoxing (args : list op) : m LLVM.value :=
    match args with
      | nil => raise "Can't box empty argument list"%string
      | arg::nil =>
        opgen arg
      | _ =>
        let size := (length args) in
        let box alloc :=
          len <- opgen (Int_o (Z.of_nat size)) ;;
          emitInstr (LLVM.Store_i false false UNIVERSAL len PTR_TYPE (%alloc) None None false) ;;
          index <- opgen (Int_o (Z.of_nat 1)) ;;
          alloc <- emitExp (LLVM.Getelementptr_e false PTR_TYPE (%alloc) ((UNIVERSAL,index)::nil)) ;;
          (fix recur index args :=
            match args with
              | nil => 
                univ <- castFrom PTR_TYPE (%alloc) ;;
                ret (%univ)
              | arg::args =>
                arg <- opgen arg ;;
                idx <- opgen (Int_o index) ;;
                let gep := LLVM.Getelementptr_e false PTR_TYPE (%alloc) ((UNIVERSAL,idx)::nil) in
                elem <- emitExp gep ;;
                emitInstr (LLVM.Store_i false false UNIVERSAL arg PTR_TYPE (%elem) None None false) ;;
                recur (index + 1)%Z args
            end) 0%Z args
        in doMalloc (size+1) box
    end.
        
  Definition generateUnboxing T (boxed : LLVM.var) (args : list Env.var) (k : m T) : m T :=
    match args with
      | nil => k
      | arg::nil =>
        withNewValue arg (%boxed) (
          addRoot arg ;;
          k
        )
      | _ =>
        boxed <- castTo PTR_TYPE (%boxed) ;;
        (fix recur index args :=
          match args with
            | nil => k
            | arg::args =>
              idx <- opgen (Int_o index) ;;
              let gep := LLVM.Getelementptr_e false PTR_TYPE (%boxed) ((UNIVERSAL,idx)::nil) in
              elem <- emitExp gep ;;
              load <- emitExp (LLVM.Load_e false false PTR_TYPE (%elem) None None None false) ;;
              withNewValue arg (%load) (
                addRoot arg ;;
                recur (index+1)%Z args
              )
          end) 0%Z args
    end.

  Definition generateCall (retVal : var) (fptr : op) (args : list op) (conts : list (cont * list op)) : m unit :=
    ptrs <- getBumpPtrs ;;
    args <- mapM opgen args ;;
    let fnArgs := (BUMP_TYPE, %ptrs, nil) ::
                  map (fun x => (UNIVERSAL, x, nil)) args in
    f <- opgen fptr ;;
    f <- castTo (computeFunctionType (length args)) f ;;
    let arity := 1 in
    match conts with
      | nil => raise "Bug?"%string (* Dead code? *)
      | ((inl 0),_)::nil =>
        let call := LLVM.Call_e true CALLING_CONV nil (RET_TYPE arity) None (%f) fnArgs nil in
        result <- emitExp call ;;
        emitInstr (LLVM.Ret_i (Some (RET_TYPE arity,%result)))
      | ((inr lbl),vars)::nil =>
        let call := LLVM.Call_e true CALLING_CONV nil (RET_TYPE arity) None (%f) fnArgs nil in
        storeRoots ;;
        result <- emitExp call ;;
        reloadRoots (
          let extractResult index :=
            emitExp (LLVM.Extractvalue_e (RET_TYPE arity) (%result) index nil)
          in
          ptrs <- extractResult 0 ;;
          result <- extractResult 1 ;;
          kArgs <- mapM opgen vars ;;
         (* Call the next continuation here *)
          withBumpPtrs ptrs (
            addJump lbl (kArgs ++ (%result)::nil) ;;
            emitInstr (LLVM.Br_uncond_i lbl)
          )
        )
      | _ => raise "Multiple continuations not supported yet"%string
    end.

  Definition ERROR_LABEL : LLVM.var := "coq_error"%string.
  
  Definition exitLabel : m LLVM.label :=
    build <- get (MonadState := State_isExit) ;;
    match build with
      | None =>
        let m :=
          let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global ERROR_LABEL) nil (LLVM.Noreturn :: nil) in
            let instr := LLVM.Assign_i None call in
              emitInstr instr ;;
              emitInstr LLVM.Unreachable_i
              in
              l <- inFreshLabel m ;;
              put (Some (fst l)) ;;
              ret (fst l)
      | Some lbl => ret lbl
    end.

  Definition generateTerm (t : Low.term) : m unit :=
    match t with
      | Halt_tm arg =>
        ptrs <- getBumpPtrs ;;
        o <- opgen arg ;;
        let args := (BUMP_TYPE, % ptrs, nil) ::
                    (UNIVERSAL, o, nil) :: nil in
        let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global HALT_LABEL) args (LLVM.Noreturn :: nil) in
        let instr := LLVM.Assign_i None call in
        emitInstr instr ;;
        emitInstr LLVM.Unreachable_i
      | Call_tm retVal fptr args conts =>
        generateCall retVal fptr args conts
      | Cont_tm cont args =>
        contArg <- generateBoxing args ;;
        match cont with
          | inl 0 =>
            let TYPE := RET_TYPE 1 in
            ptrs <- getBumpPtrs ;;
            retVal <- emitExp (LLVM.Insertvalue_e TYPE (LLVM.Constant LLVM.Undef_c) BUMP_TYPE (%ptrs) 0 nil) ;;
            retVal <- emitExp (LLVM.Insertvalue_e TYPE (%retVal) UNIVERSAL contArg 1 nil) ;;
            emitInstr (LLVM.Ret_i (Some (TYPE,(%retVal))))
          | inl _ => raise "Multiple continuations not supported yet"%string
          | inr lbl =>
            addJump lbl (contArg::nil) ;;
            emitInstr (LLVM.Br_uncond_i lbl)
        end
      | Switch_tm op arms default => 
        v <- opgen op ;;
        arms <- mapM (fun pat =>
          let '(p,target,args) := pat in
            tag <- pgen p ;;
            args <- mapM opgen args ;;
            inFreshLabel (
              addJump target args ;;
              emitInstr (LLVM.Br_uncond_i target) ;;
              ret tag
            )) arms ;;
        default <- match default with
                     | None => 
                       v <- exitLabel ;;
                       ret (v,tt)
                     | Some (target,args) =>
                       args <- mapM opgen args ;;
                       inFreshLabel (
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

  Definition withNewVars {T} (lows : list Env.var) (llvms : list LLVM.var) (k : m T) : m T :=
    (fix recur args :=
      match args with
        | nil => k
        | (a,v)::rest => withNewValue a (%v) (recur rest)
      end) (List.combine lows llvms).    

  Definition generateEntry (ps : list Env.var) (b : Low.block) : m unit :=
    let pVars := map (fun p => runShow (show p)) ps in
    withNewVars ps pVars (
      iterM addRoot ps ;;
      ptrs <- ret "bumpptrs"%string ;;
      withBumpPtrs ptrs (
        generateInstructions b
      )
    ).
 
  Definition generateBlock (l : label) (b : Low.block) : m (label * list (LLVM.var * LLVM.type)) :=
   let args := b_args b in
   let locals := b_scope b in
   argsV <- freshLLVMVar "args"%string ;;
   newLocals <- mapM freshVar locals ;;
   ptrs <- freshLLVMVar "bumpptrs"%string ;;
   withLabel l (
     withBumpPtrs ptrs (
       generateUnboxing argsV args (
         withNewVars (locals) (newLocals) (     
           iterM addRoot locals ;;
           generateInstructions b
         )
       )
     )
   ) ;;
   let args := match args with
                 | nil => nil
                 | _ => argsV::nil
               end in
   ret (l,(ptrs,BUMP_TYPE)::(map (fun v => (v,UNIVERSAL)) (newLocals ++ args))).

  Definition generateRoots : m unit :=
    roots <- getRoots ;;
    let mkRoot root :=
      let '(_,root) := root in
      emitInstr (LLVM.Assign_i (Some (%root)) (LLVM.Alloca_e PTR_TYPE (Some (UNIVERSAL, 1)) None)) ;;
      root <- emitExp (LLVM.Bitcast_e PTR_PTR_TYPE (%root) CHAR_PTR_PTR) ;;
      let args := (CHAR_PTR_PTR,%root,nil)::(CHAR_PTR,LLVM.Constant LLVM.Null_c,nil)::nil in
      let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global GCROOT) args nil in
        emitInstr (LLVM.Assign_i None call)
    in inEntryBlock (iterM mkRoot roots).

  Definition genBlocks (entryLbl : label) (params : list Env.var) (blocks : alist label block) : m (list (label * list (LLVM.var * LLVM.type))) :=
    match lookup entryLbl blocks with
      | None => raise "Entry block not found"%string
      | Some entryBlock =>
        entry <- generateEntry params entryBlock ;;
        let nonEntry := Maps.filter _ (fun l _ => negb (eq_dec l entryLbl)) blocks in
        formals <- mapM (fun block => let '(l,b) := block in generateBlock l b) nonEntry ;;
        generateRoots ;;
        ret formals
    end.

End monadic.

Section generate.
Variable m' : Type -> Type.
Context {Monad : Monad m'}.
Context {Exception : MonadExc string m'}.
Context {Trace : MonadTrace string m'}.

Definition m : Type -> Type :=
    writerT (Monoid_CFG) (readerT (map_ctor Z) (readerT LLVM.var (readerT (map_var LLVM.value)
(stateT (option LLVM.label) (stateT (list LLVM.block) (stateT LLVM.block (stateT (nat * nat) (stateT (list (Env.var * LLVM.var)) m')))))))).

Definition runM T (ctor_m : map_ctor Z) (lbl : label) (cmd : m T) : m' (T  * CFG * list LLVM.block) :=
  res <- runStateT (runStateT (runStateT (runStateT (runStateT (runReaderT (runReaderT (runReaderT (runWriterT cmd) ctor_m) "bumpptrs"%string) Maps.empty) None) nil) (Some lbl,nil)) (0,0)) nil ;;
  let '(r,cfg,_,blocks,entry,_,roots) := res in
  ret (r,cfg,entry::blocks).

Definition runGenBlocks (ctor_m : map_ctor Z) (entry : label) (params : list Env.var) (blocks : alist label block) : m' ((list (label * list (LLVM.var * LLVM.type))) * CFG * list LLVM.block) :=
  runM ctor_m entry (genBlocks (m := m) entry params blocks).

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

Definition generatePhi (f : LLVM.var * LLVM.type) (vs : list (LLVM.value * label)) : LLVM.instr :=
  let '(v,t) := f in
  LLVM.Assign_i (Some (%v)) (LLVM.Phi_e t vs).

Definition rewriteBlock (fname : string) (cfg : CFG) (formals : alist label (list (LLVM.var * LLVM.type))) (block : LLVM.block) : m' LLVM.block :=
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
                    | _ => raise ("Control-flow graph inconsisent with Low.function " ++ fname ++
                                  ": wrong number of args\n" ++
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
  end.

Fixpoint computeLocals (ps : list Env.var) (m : map_var lvar) : map_var lvar :=
  fold (fun p acc => let lv : LLVM.var := runShow (show p) in Maps.add p lv acc) Maps.empty ps.

Definition generateFunction (ctor_m : map_ctor Z) (f : Low.function) : m' LLVM.topdecl :=
  let f_params : list (LLVM.type * LLVM.var * list LLVM.param_attr) := 
    let formals :=
      Reducible.map (fun (x : Env.var) => (UNIVERSAL, runShow (show x) : string, nil : list LLVM.param_attr)) (f_args f) in
    (BUMP_TYPE,"bumpptrs"%string,nil)::formals in
  (* right return type always? *)
  let type := RET_TYPE 1 in
  let fname := cleanString (to_string (f_name f)) in
  let header := LLVM.Build_fn_header None None CALLING_CONV false type nil fname f_params nil None None GC_NAME in 
  runBlocks <- runGenBlocks ctor_m (f_entry f) (f_args f)(f_body f) ;;
  let '(formals,cfg,blocks) := runBlocks in
  phiBlocks <- mapM (rewriteBlock fname cfg formals) blocks ;;
  ret (LLVM.Define_d header phiBlocks).

End generate.
End globals.

  Definition generateGlobals (fs : list Low.function) : map_var (LLVM.value * LLVM.type) :=
    fold (fun f map =>
      let fname := f_name f in
      let cleanName := cleanString (to_string (f_name f)) in
      Maps.add fname (LLVM.Global cleanName,computeFunctionType (length (f_args f))) map) Maps.empty fs.

  Definition coq_alloc_decl : LLVM.topdecl :=
    let args := ((BUMP_TYPE,"bumpptrs",nil)::(UNIVERSAL,"words",nil)::nil)%string in
    let header := LLVM.Build_fn_header None None CALLING_CONV false ALLOC_TYPE nil "coq_alloc"%string args nil None None None in
      LLVM.Declare_d header.

  Definition coq_gc_decl : LLVM.topdecl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false BUMP_TYPE nil "coq_gc"%string nil nil None None None in
      LLVM.Declare_d header.

  Definition llvm_gcroot_decl : LLVM.topdecl :=
    let args := ((CHAR_PTR_PTR,"root",nil)::(CHAR_PTR,"metadata",nil)::nil)%string in
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "llvm.gcroot"%string args nil None None None in
      LLVM.Declare_d header.
 
  Definition coq_error_decl : LLVM.topdecl := 
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_error"%string nil nil None None None in
      LLVM.Declare_d header.

  Definition coq_report_decl : LLVM.topdecl := 
    let args := ((UNIVERSAL,"value",nil)::nil)%string in
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_report"%string args nil None None None in
      LLVM.Declare_d header.
 
  Definition coq_done_decl : LLVM.topdecl :=
    let formals := ((BUMP_TYPE,"bumpptrs",nil)::(UNIVERSAL,"o",nil)::nil)%string in
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_done"%string formals nil None None None in
      LLVM.Declare_d header.

  Definition coq_printchar_decl : LLVM.topdecl := 
    let args := ((PTR_TYPE,"ascii",nil)::nil)%string in
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil PRINTCHAR_FN args nil None None None in
      LLVM.Declare_d header.

End maps.

End sized.

Section program.
Variable m : Type -> Type.
Context {Monad : Monad m}.
Context {Exception : MonadExc string m}.
Context {Trace : MonadTrace string m}.

Variable map_ctor : Type -> Type.
Context {M_ctor : forall x, Foldable (map_ctor x) (constructor * x)}.
Context {FM_ctor : DMap constructor map_ctor}.

Definition generateProgram (word_size : nat) (mctor : map_ctor Z) (p : Low.program) : m LLVM.module :=
  let globals := generateGlobals (FM := DMap_alist RelDec_var_eq) word_size (p_topdecl p) in
  decls <- mapM (generateFunction word_size globals mctor) (p_topdecl p) ;;
  ret (coq_alloc_decl word_size :: coq_gc_decl word_size :: coq_error_decl :: coq_report_decl word_size :: coq_done_decl word_size :: llvm_gcroot_decl :: coq_printchar_decl word_size :: decls).

End program.

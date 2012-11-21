Require Import CoqCompile.Low.
Require Import CoqCompile.LLVM.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Structures.Maps.
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

Section globals.
  Variable globals : map_var (LLVM.value * LLVM.type).

Section monadic.
  Variable m : Type -> Type.
  Context {Monad : Monad m}.
  Context {Exception : MonadExc string m}.
  Context {State_fresh : MonadState (nat * nat) m}.
  Context {Reader_varmap : MonadReader (map_var lvar) m}.
  Context {Reader_ctormap : MonadReader (map_ctor Z) m}.
  Context {State_instrs : MonadState (LLVM.block) m}.
  Context {State_blks : MonadState (list LLVM.block) m}.
  Context {State_isExit : MonadState (option LLVM.label) m}.

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
  
  Definition inFreshLabel (c : m unit) : m LLVM.label :=
    st <- get (MonadState := State_instrs) ;;
    lbl <- freshLabel ;;
    put (Some lbl, nil) ;;
    c ;;
    blk' <- get (MonadState := State_instrs) ;;
    blks <- get (MonadState := State_blks) ;;
    put (blk' :: blks) ;;
    put st ;;
    ret lbl.

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

  Definition generateAlloca T (allocs : list (var * primtyp)) (k : m T) : m T.
  Admitted.

  Definition generateMalloc T (allocs : list (var * primtyp)) (k : m T) : m T.
  Admitted.

  Definition generateLoad T (dest : var) (t : primtyp) (ptr : var) (k : m T) : m T.
  Admitted.

  Definition generateStore T (t : primtyp) (v : op) (ptr : var) (k : m T) : m T.
  Admitted.

  Definition generateInstr T (i : Low.instr) (k : m T) : m T :=
    match i with
      | Primop_i v p os =>
        generatePrim v p os k
      | Alloca_i allocs =>
        generateAlloca allocs k
      | Malloc_i allocs =>
        generateMalloc allocs k
      | Load_i d t s =>
        generateLoad d t s k
      | Store_i t v d =>
        generateStore t v d k
    end.

  Definition generateTerm (t : Low.term) : m unit.
  Admitted.

  Definition generateBlock (b : Low.block) : m LLVM.label :=
    let block := (* TODO: emit phi nodes *)
      (fix recur instrs :=
        match instrs with
          | nil => generateTerm (b_term b)
          | i::rest => generateInstr i (recur rest)
        end) (b_insns b) in
      inFreshLabel block.
  
  Definition generateFunction (f : Low.function) : string + LLVM.topdecl :=
    inl "Unimplemented"%string.

  Definition coq_alloc_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false PTR_TYPE nil "coq_alloc"%string ((UNIVERSAL, "size", nil)::nil)%string nil None None None in
      LLVM.Declare_d header.
  
  Definition coq_error_decl := 
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_error"%string nil nil None None None in
      LLVM.Declare_d header.
  
  Definition coq_done_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_done"%string ((UNIVERSAL, "o", nil)::nil)%string nil None None None in
      LLVM.Declare_d header.
  
  Definition generateProgram (p : Low.program) : string + LLVM.module :=
    decls <- mapM generateFunction (p_topdecl p) ;;
    ret (coq_error_decl :: coq_done_decl :: coq_alloc_decl :: decls).

End monadic.
End globals.
End maps.
End sized.
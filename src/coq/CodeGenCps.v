Require Import CoqCompile.Lambda CoqCompile.Cps.
Require Import CoqCompile.LLVM.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Programming.Show.

Set Implicit Arguments.
Set Strict Implicit.

Module CodeGen.
  Import MonadNotation.

  Local Open Scope monad_scope.

  Definition lvar : Type := LLVM.var.

  Notation "% x" := (LLVM.Local x) (at level 50).
  (* Notation "@ x" := (LLVM.Global x) (at level 50). *)

  Section sized.
    Variable WORD_SIZE : nat.
    Definition UNIVERSAL : LLVM.type := LLVM.I_t (8 * WORD_SIZE).
    Definition ADDR_SPACE : nat := 0.

    Definition CALLING_CONV := Some LLVM.X86_fastcallcc.
    Definition GC_NAME := Some "shadow-stack"%string.

  Section maps.
    Variable map_var : Type -> Type.
    Variable map_ctor : Type -> Type.
    Context {FM : DMap Env.var map_var}.
    Context {M_ctor : forall x, Reducible (map_ctor x) (CPS.constructor * x)}.
    Context {FM_ctor : DMap CPS.constructor map_ctor}.
    
    Section globals.

      Variable globals : map_var (LLVM.value * LLVM.type).
    

  Section monadic.
    Variable m : Type -> Type.
    Variable Mon_m : Monad m.
    Variable Exc_m : MonadExc string m.
    Variable State_m : MonadState (nat * nat) m.
    Variable Reader_varmap : MonadReader (map_var lvar) m.
    Context {Reader_ctor_map : MonadReader (map_ctor Z) m}.
    Variable State_instrs : MonadState (LLVM.block) m.
    Variable State_blks : MonadState (list LLVM.block) m.
    Variable State_isExit : MonadState (option LLVM.label) m.

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

    Definition HALT_LABEL : LLVM.var := "coq_done"%string.
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
          put (Some l) ;;
          ret l
        | Some lbl => ret lbl
      end.

(*
    Definition show_map (m : map_ctor Z) : string :=
      (let show_element ctor z acc :=
        ret (Monad:=Monad_ident) (acc ++ ctor ++ ": " ++ CPS.z2string z ++ " ") in
        (unIdent (fmap_foldM (M:=Monad_ident) (K:=CPS.constructor) (show_element) "[" m)) ++ "]")%string.
*)

    Definition tagForConstructor (c : CPS.constructor) : m Z :=
      x <- ask (MonadReader := Reader_ctor_map) ;;
      match Maps.lookup c x with
        | None => raise ("error looking for '" ++ c ++ "' in TODO" (*++ show_map x*))%string
        | Some z => ret z
      end.

    (** Everything here must return something of universal type **)
    Definition PTR_TYPE := LLVM.Pointer_t ADDR_SPACE UNIVERSAL.    

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

    Definition opgen (op : CPS.op) : m LLVM.value :=
      match op with
        | CPS.Var_o v => 
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
        | CPS.Con_o c => 
          z <- tagForConstructor c ;;
          ret (LLVM.Constant (LLVM.Int_c z))
        | CPS.Int_o i => ret (LLVM.Constant (LLVM.Int_c i))
      end.

    Definition opgen_list2 (ls : list CPS.op) : m (LLVM.value * LLVM.value) :=
      match ls with
        | a :: b :: nil =>
          a <- opgen a ;;
          b <- opgen b ;;
          ret (a,b)
        | _ => 
          raise ("Expected 2 arguments got " ++ nat2string10 (length ls))%string
      end.
    
    Definition opgen_list1 (ls : list CPS.op) : m LLVM.value :=
      match ls with
        | a :: nil =>
          opgen a
        | _ => 
          raise ("Expected 1 arguments got " ++ nat2string10 (length ls))%string
      end.

    Definition primgen T (x : Env.var) (p : CPS.primop) (os : list CPS.op) (k : m T) : m T :=
      match p with
        | CPS.Eq_p =>
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Icmp_e LLVM.Eq UNIVERSAL l r) ;;
          withNewVar x y k
        | CPS.Neq_p => 
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL l r) ;;
          withNewVar x y k
        | CPS.Lt_p =>
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Icmp_e LLVM.Slt UNIVERSAL l r) ;; (** Signed? **)
          withNewVar x y k
        | CPS.Lte_p =>
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Icmp_e LLVM.Sle UNIVERSAL l r) ;;(** Signed? **)
          withNewVar x y k

        | CPS.Plus_p => 
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Add_e false false UNIVERSAL l r ) ;;
          withNewVar x y k
        | CPS.Minus_p => 
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Sub_e false false UNIVERSAL l r ) ;;
          withNewVar x y k
        | CPS.Times_p => 
          lr <- opgen_list2 os ;;
          let '(l,r) := lr in
          y <- emitExp (LLVM.Mul_e false false UNIVERSAL l r ) ;;
          withNewVar x y k

        | CPS.Ptr_p =>
          p <- opgen_list1 os ;;
          y <- emitExp (LLVM.And_e UNIVERSAL p (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
          y <- emitExp (LLVM.Icmp_e LLVM.Ne UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
          y <- emitExp (LLVM.Zext_e (LLVM.I_t 1) (%y) UNIVERSAL) ;;
          y <- emitExp (LLVM.Shl_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
          y <- emitExp (LLVM.Add_e true true UNIVERSAL (%y) (LLVM.Constant (LLVM.Int_c 1)%Z)) ;;
          withNewVar x y k

        | CPS.Proj_p =>
          lr <- opgen_list2 os ;;
          let '(idx,tpl) := lr in
          ptr <- castTo PTR_TYPE tpl ;;
          let index := (UNIVERSAL,idx) in
          let gep := LLVM.Getelementptr_e false PTR_TYPE (%ptr) (index::nil) in
          elem <- emitExp gep ;;
          y <- emitExp (LLVM.Load_e false false PTR_TYPE (%elem) None None None false) ;;
          withNewVar x y k

        | CPS.MkTuple_p =>
          x <- opgen (CPS.Var_o x) ;;
          (fix f os n : m T :=
            match os with
              | nil => k
              | o::os => 
                o <- opgen o ;;
                ptr <- castTo PTR_TYPE x ;;
                let index := (UNIVERSAL,LLVM.Constant (LLVM.Int_c (Z.of_nat n))) in
                let gep := LLVM.Getelementptr_e false PTR_TYPE (%ptr) (index::nil) in
                x <- emitExp gep ;;
                emitInstr (LLVM.Store_i false false UNIVERSAL o PTR_TYPE (%x) None None false) ;;
                f os (n+1)
            end) os 0
      end.

    Fixpoint freshLabels (n:nat) : (m (list LLVM.var)) :=
      match n with
        | O => ret nil
        | S n' => 
          x <- get ;;
          let '(v_n, l_n) := x in 
          put (v_n, S l_n) ;;
          ls <- freshLabels n' ;;
          ret (("lbl" ++ nat2string10 l_n)%string::ls)
      end.



    Definition pgen (p:CPS.pattern) : m Z :=
      match p with
        | CPS.Int_p i => ret i
        | CPS.Con_p c => 
          c <- tagForConstructor c ;;
          ret c
      end.

    Definition alloc_tuple (size : nat) : m LLVM.var :=
      let args := (UNIVERSAL, LLVM.Constant (LLVM.Int_c (Z.of_nat size)), nil)::nil in
      let call := LLVM.Call_e false CALLING_CONV nil PTR_TYPE None (LLVM.Global "coq_alloc"%string) args nil in
      ptr <- emitExp call ;;
      castFrom PTR_TYPE (%ptr).

    Definition initialize_space T (d : CPS.decl) (k : m T) : m T :=
      match d with
        | CPS.Op_d x o => 
          v <- opgen o ;;
          v' <- castTo UNIVERSAL v ;;
          withNewVar x v' k
        | CPS.Prim_d x p ds => 
          primgen x p ds k
        | _ => raise "Illegal call to initialize_space"%string
      end.

    Definition alloc_space T (d : CPS.decl) (k : m T) : m T :=
      match d with
        | CPS.Op_d x o => k
        | CPS.Prim_d x CPS.MkTuple_p ds =>
          ptr <- alloc_tuple (length ds) ;;
          withNewVar x ptr k
        | CPS.Prim_d x _ _ =>
          v <- freshVar (Env.Named_v "_"%string None) ;;
          withNewVar x v k
        | _ => raise "Call to alloc_space with invalid declaration"%string
      end.

    Fixpoint codegen (e : CPS.exp) : m unit.
    refine (
      match e with
        | CPS.App_e f args =>
          args <- mapM opgen args ;;
          let args := map (fun x => (UNIVERSAL, x, nil)) args in
          f <- opgen f ;;
          f <- castTo (LLVM.Pointer_t ADDR_SPACE (LLVM.Fn_t LLVM.Void_t (map (fun x => fst (fst x)) args) false)) f ;;
          let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (% f) args (LLVM.Noreturn :: nil) in
          let instr := LLVM.Assign_i None call in
          emitInstr instr ;;
          emitInstr LLVM.Unreachable_i
         | CPS.Let_e d e => 
          match d with
            | CPS.Op_d x o => 
              initialize_space d (codegen e)
            | CPS.Prim_d x CPS.MkTuple_p ds =>
              alloc_space d (initialize_space d (codegen e))
            | CPS.Prim_d x p ds => 
              initialize_space d (codegen e)
            | CPS.Fn_d _ _ _ => raise ("Function found in closure converted body"%string) 
            | CPS.Rec_d ds =>
              let initializations : (m unit -> m unit) :=
                (fix go ds (k : m unit) : m unit :=
                  match ds with
                    | nil => k
                    | d::rest => initialize_space d (go rest k)
                  end) ds in
              let alloc_and_init : (m unit -> m unit) :=
                (fix go ds (k : m unit) : m unit :=
                  match ds with
                    | nil => initializations k
                    | d::rest => alloc_space d (go rest k)
                  end) ds in
              alloc_and_init (codegen e)
          end
        | CPS.Switch_e o ps e =>
          v <- opgen o ;;
          arms <- mapM (fun pat =>
            let '(p,e) := pat in
            tag <- pgen p ;;
            lbl <- inFreshLabel (codegen e) ;;
            ret (UNIVERSAL, tag, lbl)) ps ;;
          defLbl <- match e with
                      | None => exitLabel
                      | Some e => inFreshLabel (codegen e)
                    end ;;
          emitInstr (LLVM.Switch_i UNIVERSAL v defLbl arms)
        | CPS.Halt_e o =>
          o <- opgen o ;;
          let args := (UNIVERSAL, o, nil) :: nil in
          let call := LLVM.Call_e true CALLING_CONV nil LLVM.Void_t None (LLVM.Global HALT_LABEL) args (LLVM.Noreturn :: nil) in
          let instr := LLVM.Assign_i None call in
          emitInstr instr ;;
          emitInstr LLVM.Unreachable_i
      end).
    Defined.

  End monadic.

  Require Import ExtLib.Data.Monads.EitherMonad.
  Require Import ExtLib.Data.Monads.ReaderMonad.
  Require Import ExtLib.Data.Monads.StateMonad.


  Definition m : Type -> Type :=
    eitherT string (readerT (map_ctor Z) (readerT (map_var lvar) (stateT (option LLVM.label) (stateT (list LLVM.block) (stateT LLVM.block (state (nat * nat))))))).
  
  Definition codegen' : CPS.exp -> m unit := @codegen m _ _ _ _ _ _ _ _.
 
  Definition runM T (locals : map_var lvar) (ctor_m : map_ctor Z) (cmd : m T) : string + (T  * list LLVM.block) :=
    let res := (runState (runStateT (runStateT (runStateT (runReaderT (runReaderT (unEitherT cmd) ctor_m) locals) None) nil) (None, nil)) (0,0)) in
    match res with
      | ((((inl e, _), _), _), _) => inl e
      | ((((inr x, _), l), b), _) => inr (x, b :: l)
    end.
  
  Definition cpsDecl2LlvmDecl (ctor_m : map_ctor Z) (d : CPS.decl) : string + LLVM.topdecl :=
    match d with
      | CPS.Fn_d f args e =>
        let f_args : list (LLVM.type * LLVM.var * list LLVM.param_attr) := 
          Reducible.map (fun (x : Env.var) => (UNIVERSAL, runShow (show x) : string, nil : list LLVM.param_attr)) args in
        let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil (runShow (show f)) f_args nil None None GC_NAME in 
        let locals : map_var lvar := fold_left (fun (acc : map_var lvar) v => 
          let lv : LLVM.var := runShow (show v) in 
          Maps.add v lv acc) args Maps.empty in
        match runM locals ctor_m (codegen' e) with
          | inl str => inl str
          | inr (_, bs) => inr (LLVM.Define_d header bs)
        end
      | _ => inl "wtf"%string
    end.
  
  Definition coq_alloc_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false PTR_TYPE nil "coq_alloc"%string ((UNIVERSAL, "size", nil)::nil)%string nil None None None in
      LLVM.Declare_d header.

  Definition coq_error_decl := 
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_error"%string nil nil None None None in
    LLVM.Declare_d header.

  Definition coq_done_decl :=
    let header := LLVM.Build_fn_header None None CALLING_CONV false LLVM.Void_t nil "coq_done"%string ((UNIVERSAL, "o", nil)::nil)%string nil None None None in
    LLVM.Declare_d header.

  Fixpoint vars_for_decl (d : CPS.decl) : list (Env.var * LLVM.type) :=
    match d with
      | CPS.Op_d x _ => (x,UNIVERSAL)::nil
      | CPS.Prim_d x CPS.MkTuple_p _ => (x,PTR_TYPE)::nil
      | CPS.Prim_d x _ _ => (x,UNIVERSAL)::nil
      | CPS.Fn_d x args _ => (x,(LLVM.Pointer_t ADDR_SPACE (LLVM.Fn_t LLVM.Void_t (map (fun x => UNIVERSAL) args) false))) :: nil
      | CPS.Rec_d ds => fold_left (@List.app _) (map vars_for_decl ds) nil
    end.

  End globals.

  Definition toModule (ctor_m : map_ctor Z) (e' : CPS.exp) : string + LLVM.module :=
    match e' with
      | CPS.Let_e (CPS.Rec_d ds) e =>
        let gmap : map_var (LLVM.value * LLVM.type) := fold_left (fun acc (entry : Env.var * LLVM.type)  =>
          match entry with
            | (v,t) => 
              let lv := runShow (show v) in
              Maps.add v (LLVM.Global lv, t) acc
          end) (vars_for_decl (CPS.Rec_d ds)) Maps.empty in
        let fMain := CPS.Fn_d (wrapVar "coq_main"%string) nil e in
        decls <- mapM (cpsDecl2LlvmDecl gmap ctor_m) (ds++(fMain::nil)) ;;
        ret (coq_alloc_decl :: coq_error_decl :: coq_done_decl :: decls)
      | _ => raise "Expecting exp to be in letrec ... in e' format"%string
    end.

End maps.
End sized.
End CodeGen.
Require Import CoqCompile.Env.
Require Import CoqCompile.CpsK CoqCompile.Lambda.
Require Import CoqCompile.AlphaEquivCpsK.
Require Import String List.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Folds.

Set Implicit Arguments.
Set Strict Implicit.

Module Cse.
  Import CPSK.

  Inductive CseValue : Type :=
  | Prim_s : primop -> list op -> CseValue
  | Fn_s   : list var -> list cont -> exp -> CseValue.

  Definition CseValue_equiv (a b : CseValue) : Prop :=
    match a , b with
      | Prim_s p os , Prim_s p' os' =>
        p = p' /\ os = os'
      | Fn_s vs ks e , Fn_s vs' ks' e' =>
        Alpha.alpha_lam e e' vs vs' ks ks' = true
      | _ , _ => False
    end.

  Instance RelDec_CseValue_eq : RelDec (@eq CseValue) :=
  { rel_dec a b :=
    match a , b with
      | Prim_s p os , Prim_s p' os' =>
        if eq_dec p p' then eq_dec os os' else false
      | Fn_s vs ks e , Fn_s vs' ks' e' =>
        Alpha.alpha_lam e e' vs vs' ks ks'
      | _ , _ => false
    end }.

  Section with_env.
    Variable env_v : Type -> Type.
    Variable env_e : Type -> Type.
    Context {Mv : DMap var env_v}.
    Context {Me : DMap CseValue env_e}.

    Section monadic.
      Variable m : Type -> Type.
      Context {Mon_m : Monad m}.
      Context {Reader_m : MonadReader (env_v op * env_e op) m}.
      
      Import MonadNotation.
      Local Open Scope monad_scope.

      Definition cse_op (o : op) : m op :=
        match o with
          | Var_o v => 
            x <- ask ;;
            match Maps.lookup v (fst x) with
              | None => ret (Var_o v)
              | Some o => ret o
            end
          | o => ret o 
        end.

      Definition use_op {T} (v : var) (o : op) : m T -> m T :=
        local (fun x => (add v o (fst x), snd x)).

      Definition remember_def {T} (o : var) (v : CseValue) : m T -> m T :=
        local (fun x => (add o (Var_o o) (fst x), add v (Var_o o) (snd x))).

      Definition under_vars {T} (vs : list var) : m T -> m T :=
        local (fun x => 
          (fold_left (fun acc x => add x (Var_o x) acc) vs (fst x),
           snd x)).      

      (** NOTE: This assumes no aliasing **)
      Fixpoint cse_decl {T} (d : decl) (cc : decl -> m T) : m T :=
        match d with
          | Op_d v o => 
            o <- cse_op o ;;
            use_op v o (cc (Op_d v o))
          | Prim_d v p os =>
            os <- mapM cse_op os ;;
            x <- ask ;;
            match Maps.lookup (Prim_s p os) (snd x) with
              | None => remember_def v (Prim_s p os) (cc (Prim_d v p os))
              | Some o => use_op v o (cc (Op_d v o))
            end
          | Bind_d v w m os =>
            os <- mapM cse_op os ;;
            use_op v (Var_o v) (use_op w (Var_o w) (cc (Bind_d v w m os)))
          | Fn_d v ks vs e =>
            e <- under_vars vs (cse_exp e) ;;
            x <- ask ;;
            match Maps.lookup (Fn_s vs ks e) (snd x) with
              | None => 
                remember_def v (Fn_s vs ks e) (cc (Fn_d v ks vs e))
              | Some o => use_op v o (cc (Op_d v o))
            end
        end
      with cse_exp (e : exp) : m exp :=
        match e with
          | App_e f ks xs =>
            f <- cse_op f ;;
            xs <- mapM cse_op xs ;;
            ret (App_e f ks xs)
          | Let_e ds e =>
            cse_decl ds (fun ds =>
              e <- cse_exp e ;;
              ret (Let_e ds e))
          | Letrec_e ds e =>
            (fix go ds acc k :=
              match ds with
                | nil => k acc
                | d :: ds => 
                  cse_decl d (fun d =>
                    go ds (d :: acc) k)
              end) ds nil (fun ds =>
                e <- cse_exp e ;;
                ret (Letrec_e ds e))
          | Switch_e o br def =>
            o <- cse_op o ;;
            br <- mapM (fun p_e => 
              let (p,e) := p_e : pattern * exp in
              e <- cse_exp e ;; ret (p, e)) br ;;
            def <- match def with
                     | None => ret None
                     | Some def => def <- cse_exp def ;; ret (Some def)
                   end ;;
            ret (Switch_e o br def)
          | Halt_e o o' =>
            o <- cse_op o ;;
            o' <- cse_op o' ;;
            ret (Halt_e o o')
          | AppK_e k xs =>
            xs <- mapM cse_op xs ;;
            ret (AppK_e k xs)
          | LetK_e ks e =>
            ks <- mapM (fun kxse => let '(k,xs,e) := kxse in
              e <- under_vars xs (cse_exp e) ;;
              ret (k, xs, e)) ks ;;              
            e <- cse_exp e ;;
            ret (LetK_e ks e)
        end.

    End monadic.

  End with_env.

  Require Import ExtLib.Data.Monads.ReaderMonad.
  
  Definition cse (e : exp) : exp :=
    runReader (cse_exp e) (empty, empty).

(*
  Section Tests.
    Import LambdaNotation.
    Require Import CoqCompile.CpsKConvert.
    Require Import ExtLib.Data.Map.FMapAList.

    Definition cse1 := def y := S_c Z_c in def z := S_c Z_c in S_c y.
    
    Eval compute in (exp2string (CPS_pure (gen cse1))).
    Eval compute in (exp2string (cse (CPS_pure (gen cse1)))).

    Definition cse2 := def y := \ x => x in def z := \ y => y in z.
    
    Eval compute in (exp2string (CPS_pure (gen cse2))).
    Eval compute in (exp2string (cse (CPS_pure (gen cse2)))).

    Eval compute in (exp2string (CPS_pure (gen e8))).
    Eval compute in (exp2string (cse (CPS_pure (gen e8)))).
  End Tests.
*)

End Cse.
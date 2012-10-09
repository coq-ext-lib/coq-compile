Require Import CoqCompile.Env.
Require Import CoqCompile.Cps CoqCompile.Lambda.
Require Import CoqCompile.Opt.AlphaCps.
Require Import String List.
Require Import ExtLib.Decidables.Decidable.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.ReaderMonad.
Require Import ExtLib.Monad.Folds.

Set Implicit Arguments.
Set Strict Implicit.

Module Cse.
  Import CPS.

  Inductive CseValue : Type :=
  | Prim_s : primop -> list op -> CseValue
  | Fn_s   : list var -> exp -> CseValue.

  Definition CseValue_equiv (a b : CseValue) : Prop :=
    match a , b with
      | Prim_s p os , Prim_s p' os' =>
        p = p' /\ os = os'
      | Fn_s vs e , Fn_s vs' e' =>
        Alpha.alpha_lam e e' vs vs' = true
      | _ , _ => False
    end.

  Instance RelDec_CseValue_eq : RelDec (@eq CseValue) :=
  { rel_dec a b :=
    match a , b with
      | Prim_s p os , Prim_s p' os' =>
        if eq_dec p p' then eq_dec os os' else false
      | Fn_s vs e , Fn_s vs' e' =>
        Alpha.alpha_lam e e' vs vs'
      | _ , _ => false
    end }.

  Section with_env.
    Variable env_v : Type -> Type.
    Variable env_e : Type -> Type.
    Context {Mv : Map var env_v}.
    Context {Me : Map CseValue env_e}.

    Section monadic.
      Variable m : Type -> Type.
      Context {Mon_m : Monad m}.
      Context {Reader_m : Reader (env_v var * env_e op) m}.
      
      Import MonadNotation.
      Local Open Scope monad_scope.
      
      Definition cse_op (o : op) : m op :=
        match o with
          | Var_o v => 
            x <- ask ;;
            match FMaps.lookup v (fst x) with
              | None => ret (Var_o v)
              | Some v => ret (Var_o v)
            end
          | o => ret o 
        end.

      (** NOTE: This assumes no aliasing **)
      Fixpoint cse_decl {T} (d : decl) (cc : decl -> m T) : m T :=
        match d with
          | Op_d v o => 
            o <- cse_op o ;;
            cc (Op_d v o)
          | Prim_d v p os =>
            os <- mapM cse_op os ;;
            x <- ask ;;
            match FMaps.lookup (Prim_s p os) (snd x) with
              | None => local (fun x => (fst x, add (Prim_s p os) (Var_o v) (snd x))) (cc (Prim_d v p os))
              | Some o => cc (Op_d v o)
            end
          | Fn_d v vs e =>
            x <- ask ;;
            match FMaps.lookup (Fn_s vs e) (snd x) with
              | None => local (fun x => (fst x, add (Fn_s vs e) (Var_o v) (snd x))) (cc (Fn_d v vs e))
              | Some o => cc (Op_d v o)
            end
          | Rec_d ds =>
            ds <- mapM (fun x => cse_decl x ret) ds ;;
            cc (Rec_d ds)
        end
      with cse_exp (e : exp) : m exp :=
        match e with
          | App_e f xs =>
            f <- cse_op f ;;
            xs <- mapM cse_op xs ;;
            ret (App_e f xs)
          | Let_e ds e =>
            cse_decl ds (fun ds =>
              e <- cse_exp e ;;
              ret (Let_e ds e))
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
          | Halt_e o =>
            o <- cse_op o ;;
            ret (Halt_e o)
        end.

    End monadic.

  End with_env.
  
  Definition cse (e : exp) : exp :=
    runReader (cse_exp e) (empty, empty).

  Section Tests.
    Import LambdaNotation.
    Require Import ExtLib.FMaps.FMapAList.

    Definition cse1 := def y := S_c Z_c in def z := S_c Z_c in S_c y.
    
    Eval compute in (exp2string (CPS (gen cse1))).
    Eval compute in (exp2string (cse (CPS (gen cse1)))).

    Definition cse2 := def y := \ x => x in def z := \ y => y in z.
    
    Eval compute in (exp2string (CPS (gen cse2))).
    Eval compute in (exp2string (cse (CPS (gen cse2)))).
  End Tests.

End Cse.
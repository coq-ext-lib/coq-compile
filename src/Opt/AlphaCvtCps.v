Require Import String.
Require Import CoqCompile.Cps CoqCompile.CpsUtil.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Structures.Monoid.
Require Import List.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Reducible.
Require Import Data.Strings.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Core.RelDec.
Require Import BinPos.

Set Implicit Arguments.
Set Strict Implicit.

(** This module provides a function [alpha_cvt] that renames
    a CPS expression systematically using fresh names everywhere.
    It's useful for restoring the unique name invariant after some
    optimization pass such as after inlining functions.
*)
Module AlphaCvt.
  Import CPS.

  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : DMap var env_v}.
    Context {FMv : forall V, Foldable (env_v V) (var * V)}.
    Section monadic.
      Variable M : Type -> Type.
      Context {Monad_m : Monad M}.
      Context {State_m : MonadState positive M}.
      Context {Reader_m : MonadReader (env_v var) M}.

      Import MonadNotation.
      Open Local Scope monad_scope.

      Definition freshFor (v: var) : M var := 
        n <- modify Psucc ;; 
        match v with
          | Env.Anon_v _ => 
            ret (Env.Anon_v n)
          | Env.Named_v s _ => 
            ret (Env.Named_v s (Some n))
        end.

      Definition alpha_op (v:op) : M op := 
        match v with 
          | Var_o x => 
            env <- ask ; match Maps.lookup x env with 
                           | None => ret v
                           | Some y => ret (Var_o y)
                         end
          | _ => ret v
        end.

      Definition overlay (e1 : env_v var) (e2 : env_v var) : env_v var := 
        combine (fun x y z => z) e2 e1.

      Fixpoint overlay_list (xs ys:list var)(env:env_v var) : env_v var := 
        match xs, ys with 
          | x::xs, y::ys => overlay_list xs ys (add x y env)
          | _, _ => env
        end.

      Definition fresh_or_rec (rec:bool) (x:var) : M var := 
        if rec then 
          env <- ask ; 
          match lookup x env with 
            | None => ret x
            | Some y => ret y
          end
        else freshFor x.

      Definition alpha_rec_decl (d:decl) : M (env_v var) := 
        match d with 
          | Fn_d f _ _ => f' <- freshFor f ;; ret (singleton f f')
          | Op_d x _ => x' <- freshFor x ;; ret (singleton x x')
          | Prim_d x _ _ => x' <- freshFor x ;; ret (singleton x x')
          | Bind_d x w _ _ => x' <- freshFor x ;; w' <- freshFor w ;; ret (union (singleton x x') (singleton w w'))
          (* | Rec_d ds =>  *)
          (*   (fix alpha_rec_decls (ds:list decl) : M (env_v var) :=  *)
          (*     match ds with  *)
          (*       | nil => ret empty *)
          (*       | d::ds => env1 <- alpha_rec_decl d ;  *)
          (*         env2 <- alpha_rec_decls ds ;  *)
          (*         ret (overlay env2 env1) *)
          (*     end) ds *)
        end.

      Fixpoint alpha_exp (e:exp) : M exp := 
        match e return M exp with 
          | Halt_e v => v' <- alpha_op v ; ret (Halt_e v')
          | App_e v vs => 
            v' <- alpha_op v ;;
            vs' <- mapM alpha_op vs ;;
            ret (App_e v' vs')
          | Switch_e v arms def => 
            v' <- alpha_op v ;;
            arms' <- 
              mapM (fun p => e' <- alpha_exp (snd p) ; ret (fst p, e')) arms ; 
            def' <- match def return M (option exp) with 
                      | None => ret None 
                      | Some e => e' <- alpha_exp e ; ret (Some e') 
                    end ;;
            ret (Switch_e v' arms' def')
          | Let_e d e => 
            p <- alpha_decl false d ;;
            let (d', env) := p in 
              e' <- local (overlay env) (alpha_exp e) ;;
              ret (Let_e d' e')
          | Letrec_e ds e =>
            defs <- reduceM (ret empty) (alpha_rec_decl) (fun x y => ret (union x y)) ds ;;
            let _ : env_v var := defs in
            local (overlay defs) 
              (ds' <- mapM (fun d => p <- alpha_decl true d ;; ret (fst p)) ds ;;
               e' <- alpha_exp e ;;
               ret (Letrec_e ds' e'))
        end
      with alpha_decl (recursive:bool) (d:decl) : M (decl * env_v var) := 
        match d with 
          | Op_d x v => 
            x' <- fresh_or_rec recursive x ;;
            v' <- alpha_op v ;;
            ret (Op_d x' v', singleton x x')
          | Prim_d x p vs => 
            x' <- fresh_or_rec recursive x ;;
            vs' <- mapM alpha_op vs ;;
            ret (Prim_d x' p vs', singleton x x')
          | Bind_d x w m vs => 
            x' <- fresh_or_rec recursive x ;;
            w' <- fresh_or_rec recursive w ;;
            vs' <- mapM alpha_op vs ;;
            ret (Bind_d x' w' m vs', singleton x x')
          | Fn_d f xs e => 
            f' <- fresh_or_rec recursive f ;;
            xs' <- mapM freshFor xs ;; 
            e' <- local (overlay_list xs xs') (alpha_exp e) ;;
            ret (Fn_d f' xs' e', singleton f f')
        end.
    End monadic.
  End maps.

  Require Import ExtLib.Data.Monads.WriterMonad.
  Require Import ExtLib.Data.Monads.ReaderMonad.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Map.FMapAList.

  Require Import CoqCompile.Env.

  Definition alpha_cvt (e:exp) : exp := 
    let env_v := alist var in 
    let c := alpha_exp (env_v := alist var) (M := readerT (env_v var) (state positive)) e in 
    evalState (runReaderT c empty) 1%positive.

(*
  Module Tests.
    Require Import Lambda.
    Import LambdaNotation.

    Eval compute in (exp2string (CPS (gen e1))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e1)))).
    Eval compute in (exp2string (alpha_cvt (alpha_cvt (CPS (gen e1))))).
    Eval compute in (exp2string (CPS (gen e2))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e2)))).
    Eval compute in (exp2string (CPS (gen e3))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e3)))).
    Eval compute in (exp2string (CPS (gen e4))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e4)))).
    Eval compute in (exp2string (CPS (gen e5))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e5)))).
    Eval compute in (exp2string (CPS (gen e6))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e6)))).
    Eval compute in (exp2string (CPS (gen e7))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e7)))).
    Eval compute in (exp2string (CPS (gen e8))).
    Eval compute in (exp2string (alpha_cvt (CPS (gen e8)))).
  End Tests.
*)

End AlphaCvt.
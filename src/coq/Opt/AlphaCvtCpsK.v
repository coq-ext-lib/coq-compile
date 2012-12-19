Require Import String.
Require Import CoqCompile.CpsK CoqCompile.CpsKUtil.
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
  Import CPSK.

  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : DMap var env_v}.
    Context {FMv : forall V, Foldable (env_v V) (var * V)}.
    Variable env_k : Type -> Type.
    Context {Mv_k : DMap cont env_k}.
    Context {FMv_k : forall V, Foldable (env_k V) (cont * V)}.

    Section monadic.
      Variable M : Type -> Type.
      Context {Monad_m : Monad M}.
      Context {State_m : MonadState positive M}.
      Context {Reader_m : MonadReader (env_v var) M}.
      Context {Reader_mk : MonadReader (env_k cont) M}.

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

      Definition freshK (v: cont) : M cont := 
        n <- modify Psucc ;; 
        ret match v with
              | K name _ => K name n
            end.

      Definition alpha_op (v:op) : M op := 
        match v with 
          | Var_o x => 
            x <- asks (Maps.lookup x) ;;
            match x with 
              | None => ret (Var_o (Env.Named_v "___BAD" None))
              | Some y => ret (Var_o y)
            end
          | _ => ret v
        end.

      Definition alpha_k (k : cont) : M cont :=
        x <- asks (Maps.lookup k) ;;
        match x with
          | None => ret (K "___BAD" 1)
          | Some y => ret y
        end.

      Definition overlay (e1 : env_v var) (e2 : env_v var) : env_v var := 
        combine (fun x y z => z) e2 e1.

      Definition overlayK (e1 : env_k cont) (e2 : env_k cont) : env_k cont := 
        combine (fun x y z => z) e2 e1.

      Fixpoint overlay_list (xs ys:list var)(env:env_v var) : env_v var := 
        match xs, ys with 
          | x::xs, y::ys => overlay_list xs ys (add x y env)
          | _, _ => env
        end.

      Fixpoint overlay_listK (xs ys:list cont)(env:env_k cont) : env_k cont := 
        match xs, ys with 
          | x::xs, y::ys => overlay_listK xs ys (add x y env)
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
          | Fn_d f _ _ _ => f' <- freshFor f ;; ret (singleton f f')
          | Op_d x _ => x' <- freshFor x ;; ret (singleton x x')
          | Prim_d x _ _ => x' <- freshFor x ;; ret (singleton x x')
          | Bind_d x w _ _ => x' <- freshFor x ;; w' <- freshFor w ;; ret (union (singleton x x') (singleton w w'))
        end.

      Fixpoint alpha_exp (e:exp) : M exp := 
        match e return M exp with 
          | Halt_e v v' => liftM2 Halt_e (alpha_op v) (alpha_op v')
          | LetK_e ks e =>
            defs <- reduceM (ret empty) (fun k => let '(k,_,_) := k in
              k' <- freshK k ;; ret (singleton k k')) (fun x y => ret (union x y)) ks ;;
            let _ : env_k cont := defs in
            local (overlayK defs) 
              (ks' <- mapM (fun k => let '(k,xs,e) := k in
                xs' <- mapM freshFor xs ;;
                e <- local (overlay_list xs xs') (alpha_exp e) ;;
                k' <- alpha_k k ;;
                ret (k', xs', e)) ks ;;
               e' <- alpha_exp e ;;
               ret (LetK_e ks' e'))
          | AppK_e k xs =>
            liftM2 AppK_e (alpha_k k) (mapM alpha_op xs)
          | App_e v ks vs => 
            v' <- alpha_op v ;;
            ks' <- mapM alpha_k ks ;;
            vs' <- mapM alpha_op vs ;;
            ret (App_e v' ks' vs')
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
            ret (Bind_d x' w' m vs', add w w' (singleton x x'))
          | Fn_d f ks xs e => 
            f' <- fresh_or_rec recursive f ;;
            xs' <- mapM freshFor xs ;; 
            ks' <- mapM freshK ks ;; 
            e' <- local (overlay_listK ks ks') (local (overlay_list xs xs') (alpha_exp e)) ;;
            ret (Fn_d f' ks' xs' e', singleton f f')
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
    let env_k := alist cont in 
    let c := alpha_exp (env_v := env_v) (M := readerT (env_v var) (readerT (env_k cont) (state positive))) e in 
    evalState (runReaderT (runReaderT c empty) empty) 1%positive.

(*
  Module Tests.
    Require Import Lambda.
    Require Import CoqCompile.CpsKConvert.
    Import LambdaNotation.

    Eval compute in (exp2string (CPS_pure (gen e1))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e1)))).
    Eval compute in (exp2string (alpha_cvt (alpha_cvt (CPS_pure (gen e1))))).
    Eval compute in (exp2string (CPS_pure (gen e2))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e2)))).
    Eval compute in (exp2string (CPS_pure (gen e3))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e3)))).
    Eval compute in (exp2string (CPS_pure (gen e4))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e4)))).
    Eval compute in (exp2string (CPS_pure (gen e5))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e5)))).
    Eval compute in (exp2string (CPS_pure (gen e6))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e6)))).
    Eval compute in (exp2string (CPS_pure (gen e7))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e7)))).
    Eval compute in (exp2string (CPS_pure (gen e8))).
    Eval compute in (exp2string (alpha_cvt (CPS_pure (gen e8)))).
  End Tests.
*)

End AlphaCvt.
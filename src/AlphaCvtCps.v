Require Import String.
Require Import CoqCompile.Cps CoqCompile.CpsUtil.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Data.Monoid.
Require Import List.
Require Import ExtLib.Functor.Functor.
Require Import ExtLib.Functor.Traversable.
Require Import Data.Strings.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.Decidables.Decidable.

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
    Context {Mv : Map var env_v}.
    Context {FMv : FMap var env_v}.
    Section monadic.
      Variable M : Type -> Type.
      Context {Monad_m : Monad M}.
      Context {State_m : State nat M}.
      Context {Reader_m : Reader (env_v var) M}.

      Import MonadNotation.
      Open Local Scope monad_scope.

      Definition fresh (s:string) : M var := 
        n <- get ;; 
        put (S n) ;; 
        ret ("%x" ++ nat2string10 n)%string.

      Definition alpha_op (v:op) : M op := 
        match v with 
          | Var_o x => 
            env <- ask ; match FMaps.lookup x env with 
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

      Definition fresh_or_rec (rec:bool) (x:string) : M var := 
        if rec then 
          env <- ask ; 
          match FMaps.lookup x env with 
            | None => ret x
            | Some y => ret y
          end
          else fresh x.

      Fixpoint alpha_rec_decl (d:decl) : M (env_v var) := 
        match d with 
          | Fn_d f _ _ => f' <- fresh f ; ret (singleton f f')
          | Op_d x _ => x' <- fresh x ; ret (singleton x x')
          | Prim_d x _ _ => x' <- fresh x ; ret (singleton x x')
          | Rec_d ds => 
            (fix alpha_rec_decls (ds:list decl) : M (env_v var) := 
              match ds with 
                | nil => ret empty
                | d::ds => env1 <- alpha_rec_decl d ; 
                  env2 <- alpha_rec_decls ds ; 
                  ret (overlay env2 env1)
              end) ds
        end.
      Definition alpha_rec_decls ds := alpha_rec_decl (Rec_d ds).

      Fixpoint alpha_exp (e:exp) : M exp := 
        match e with 
          | Halt_e v => v' <- alpha_op v ; ret (Halt_e v')
          | App_e v vs => 
            v' <- alpha_op v ; 
            vs' <- mapM alpha_op vs ; 
            ret (App_e v' vs')
          | Switch_e v arms def => 
            v' <- alpha_op v ; 
            arms' <- 
              mapM (fun p => e' <- alpha_exp (snd p) ; ret (fst p, e')) arms ; 
            def' <- match def return M (option exp) with 
                      | None => ret None 
                      | Some e => e' <- alpha_exp e ; ret (Some e') 
                    end ; 
            ret (Switch_e v' arms' def')
          | Let_e d e => 
            p <- alpha_decl false d ; 
            let (d', env) := p in 
              e' <- local (overlay env) (alpha_exp e) ; 
              ret (Let_e d' e')
        end
      with alpha_decl (recursive:bool) (d:decl) : M (decl * env_v var) := 
        match d with 
          | Op_d x v => 
            x' <- fresh_or_rec recursive x ; 
            v' <- alpha_op v ; 
            ret (Op_d x' v', singleton x x')
          | Prim_d x p vs => 
            x' <- fresh_or_rec recursive x ; 
            vs' <- mapM alpha_op vs ; 
            ret (Prim_d x' p vs', singleton x x')
          | Fn_d f xs e => 
            f' <- fresh_or_rec recursive f ; 
            xs' <- mapM fresh xs ; 
            e' <- local (overlay_list xs xs') (alpha_exp e) ;
            ret (Fn_d f' xs' e', singleton f f')
          | Rec_d ds => 
            env <- alpha_rec_decls ds ; 
            ds' <- mapM (fun d => p <- local (overlay env) (alpha_decl true d) ; 
                                  ret (fst p)) ds ; 
            ret (Rec_d ds', env)
        end.
    End monadic.
  End maps.

  Require Import ExtLib.FMaps.FMapAList.
  Require Import ExtLib.Monad.WriterMonad.
  Require Import ExtLib.Monad.ReaderMonad.
  Require Import ExtLib.Monad.StateMonad.

  Definition alpha_cvt (e:exp) : exp := 
    let env_v := alist var in 
      let c := alpha_exp (env_v := env_v) (M := readerT (env_v var) (state nat)) e
        in 
        fst (runState (runReaderT c empty) 0).

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
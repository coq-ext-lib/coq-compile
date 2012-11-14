Require Import CoqCompile.Cps.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import BinPos.

Set Implicit Arguments.
Set Strict Implicit.

(** This file implements a pass that counts the occurances of each variable **)
Module Occurs.
  Import CPS.

  Section with_maps.
    Variable map_v : Type -> Type.
    Context {DMap_map_v : DMap var map_v}.

    Section monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {Reader_m : MonadState (map_v positive) m}.
      
      Import MonadNotation.
      Local Open Scope monad_scope.

      Definition use_var (v : var) : m unit :=
        modify (fun x : map_v positive => 
          match Maps.lookup v x with
            | None => add v 1%positive x
            | Some n => add v (Psucc n) x
          end) ;;
        ret tt.
      
      Definition use_pat (p : pattern) : m unit := ret tt.

      Definition use_op (o : op) : m unit :=
        match o with
          | Var_o x => use_var x
          | _ => ret tt
        end.

      Fixpoint use_exp (e : exp) : m unit := 
        match e with
          | App_e f xs => use_op f ;; iterM use_op xs
          | Let_e d e => use_decl d ;; use_exp e
          | Letrec_e ds e => iterM use_decl ds ;; use_exp e 
          | Switch_e x ls d => 
            use_op x ;;
            iterM (fun pe => use_exp (snd pe)) ls ;;
            iterM use_exp d
          | Halt_e o => use_op o
        end
      with use_decl (d : decl) : m unit :=
        match d with
          | Op_d _ o => use_op o
          | Prim_d _ _ ls => iterM use_op ls
          | Fn_d _ _ e => use_exp e
          | Bind_d _ _ _ ls => iterM use_op ls
        end.
      
    End monadic.

    Require Import ExtLib.Data.Monads.StateMonad.

    Definition uses (e : exp) : map_v positive :=
      execState (use_exp e) empty.
  End with_maps.
End Occurs.
Require Import CoqCompile.Lambda CoqCompile.Env.
Require Import ExtLib.Data.Strings.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Folds.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.ZDecidables.
Require Import ExtLib.Core.PosDecidables.
Require Import ExtLib.Structures.Maps.
Require Import CoqCompile.CpsK.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation. 
Local Open Scope monad_scope.
Definition constructor := Lambda.constructor.
Definition env_t := Lambda.env_t.

Definition label := string.
Definition fname := var.

Inductive primtyp :=
| Int_t : primtyp
| Ptr_t : primtyp -> primtyp
| Struct_t : list primtyp -> primtyp.


(*
Definition op := CpsK.CPS.op.
Definition pattern := CpsK.CPS.pattern.
*)

Inductive primop :=
| Eq_p
| Neq_p
| Lt_p
| Lte_p
| Ptr_p
| Plus_p
| Minus_p 
| Times_p. 

Inductive instr :=
| Primop_i : var -> primop -> list op -> instr
| Push_i : primtyp -> instr
| Pop_i : var -> primtyp -> instr
| Alloca_i : list (var * primtyp) -> instr
| Malloc_i : list (var * primtyp) -> instr
| Load_i : primtyp -> var -> instr
| Store_i : primtyp -> op -> var -> instr.

(* A function can be called with a list of continuations that were either 
   passed as arguments (referred to by the index of the formal) or that 
   were bound locally (referred to by the label of the generated code block
   and a list of arguments, which may include the return value). *)
Definition cont : Type := (nat + (label * list op))%type.

Inductive term :=
| Call_tm : var -> fname -> list op -> list cont -> term
(* Return to a passed-in continuation *)
| Cont_tm : nat -> list op -> term
| Switch_tm : op -> list (pattern * label * list op) -> option (label * list op) -> term.

Record block := mk_block {
  b_args : list var;
  b_insns : list instr;
  b_term : term
}.

Record function := mk_function {
  f_name : fname;
  f_args : list var;
  f_body : label -> block
}.

Record program := mk_program {
  p_topdecl : list function;
  p_entry : fname
}.

Section maps.
  Variable map_var : Type -> Type.
  Context {FM : DMap Env.var map_var}.

Section monadic.
  Variable m : Type -> Type.
  Variable State_blks : MonadState (list block) m.
  (*
  Variable Mon_m : Monad m.
  Variable State_m : MonadState (nat * nat) m.
  Variable Reader_varmap : MonadReader (map_var lvar) m.
  Context {Reader_ctor_map : MonadReader (map_ctor Z) m}.
  Variable State_instrs : MonadState (LLVM.block) m.
  Variable State_blks : MonadState (list LLVM.block) m.
  Variable State_isExit : MonadState (option LLVM.label) m.
  *)

  Definition prim2low (p:CpsCommon.primop) : option primop :=
    match p with
      | CpsCommon.Eq_p => Some Eq_p
      | CpsCommon.Neq_p => Some Neq_p
      | CpsCommon.Lt_p => Some Lt_p
      | CpsCommon.Lte_p => Some Lte_p
      | CpsCommon.Ptr_p => Some Ptr_p
      | CpsCommon.Plus_p => Some Plus_p
      | CpsCommon.Minus_p => Some Minus_p
      | CpsCommon.Times_p => Some Times_p
      | CpsCommon.MkTuple_p => None
      | CpsCommon.Proj_p => None
    end.
  
(*
  Fixpoint cps2low (e:Cps.CPS.exp) : m _ .
  refine (
    match e with
      | App_e o k os => 
        
      | Let_e d e => _
      | Letrec_e ds e => _
      | Switch_e o arms e => _
      | Halt_e o => _
    end).
*)

End monadic.
End maps.

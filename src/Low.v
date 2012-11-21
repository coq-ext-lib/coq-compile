Require Import String.
Require Import CoqCompile.Lambda CoqCompile.Env.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.CpsK.

Set Implicit Arguments.
Set Strict Implicit.

Definition constructor := Lambda.constructor.
Definition env_t := Lambda.env_t.

Definition label := string.
Definition fname := var.

Inductive primtyp :=
| Int_t : primtyp
| Ptr_t : primtyp -> primtyp
| Struct_t : list primtyp -> primtyp.

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
| Alloca_i : list (var * primtyp) -> instr
| Malloc_i : list (var * primtyp) -> instr
(* Load_i(value,type,offset,pointer) *)
| Load_i : var -> primtyp -> nat -> var -> instr
| Store_i : primtyp -> op -> nat -> var -> instr.

(* A function can be called with a list of continuations that were either 
   passed as arguments (referred to by the index of the formal) or that 
   were bound locally (referred to by the label of the generated code block
   and a list of arguments, which may include the return value). *)
Definition cont : Type := (nat + label)%type.

Inductive term :=
| Halt_tm : op -> term
| Call_tm : var -> op -> list op -> list cont -> term
(* Return to a passed-in continuation *)
| Cont_tm : cont -> list op -> term
| Switch_tm : op -> list (pattern * label * list op) -> option (label * list op) -> term.

Record block := mk_block {
  b_args : list var;
  b_insns : list instr;
  b_term : term
}.

Record function := mk_function {
  f_name : fname;
  f_args : list var;
  f_body : alist label block
}.

Record program := mk_program {
  p_topdecl : list function;
  p_entry : fname
}.
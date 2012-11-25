Require Import ZArith String.
Require Import CoqCompile.Lambda CoqCompile.Env.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.CpsK.
Require Import List.

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
| Load_i : var -> primtyp -> Z -> var -> instr
| Store_i : primtyp -> op -> Z -> var -> instr.

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
  f_name  : fname ;
  f_args  : list var ;
  f_conts : nat ;
  f_body  : alist label block ; 
  f_entry : label
}.

Record program := mk_program {
  p_topdecl : list function ;
  p_entry : fname
}.

Section Printing.
  Require Import ExtLib.Programming.Show.
  Require Import ExtLib.Core.RelDec.
  Require Import ExtLib.Structures.Reducible.
  Require Import ExtLib.Data.Char.
  Import ShowNotation.
  Local Open Scope string_scope.
  Local Open Scope show_scope.

  Global Instance Show_primtyp : Show primtyp :=
  { show := fix show_primtyp p : showM :=
    match p return showM with
      | Int_t => "int"
      | Ptr_t t => "ptr(" << show_primtyp t << ")"
      | Struct_t ls => "<" << sepBy "," (map show_primtyp ls) << ">"
    end }.

  Global Instance Show_fname : Show fname :=
  { show := fun fn => show fn }.

  Global Instance Show_primop : Show primop :=
  { show := fun p =>
    match p with
      | Eq_p    => "eq?"
      | Neq_p   => "neq?"
      | Lt_p    => "lt?"
      | Lte_p   => "lte?"
      | Ptr_p   => "ptr?"
      | Plus_p  => "plus"
      | Minus_p => "sub"
      | Times_p => "mult"
    end }.

  Global Instance Show_instr : Show instr :=
  { show := fun i =>
    match i with
      | Primop_i v p os => show v << " = " << show p << "(" << sepBy ", " (map show os)
      | Alloca_i vs => "[" << sepBy "," (map (fun x => show (fst x)) vs) <<
        "] = alloc(" << sepBy "," (map (fun x => show (snd x)) vs) << ")"
      | Malloc_i vs => "[" << sepBy "," (map (fun x => show (fst x)) vs) <<
        "] = malloc(" << sepBy "," (map (fun x => show (snd x)) vs) << ")"
      | Load_i x t d v => show x << " = load " << show t << " from " << show v << " + " << show d
      | Store_i t o d v => 
        "store " << show o << "@" << show t << " into " << show v << " + " << show d
    end }.

  Global Instance Show_cont : Show cont :=
  { show := fun c =>
    match c with
      | inl c => "$" << show c
      | inr v => "$" << show v
    end }.

  Global Instance Show_term : Show term :=
  { show := fun t =>
    match t with
      | Halt_tm o => "halt " << show o
      | Call_tm v fn args ks => 
        show v << " = " << show fn << "(" << sepBy "," (map show args) << ") return ["
        << sepBy "," (map show ks) << "]"
      | Cont_tm k args => "return " << show k << "(" << sepBy "," (map show args) << ")"
      | Switch_tm o ps def =>
        "switch " << show o 
        << indent "  " (sepBy chr_newline (map (fun plos => let '(p,l,os) := plos in
          "| " << show p << " => " << show l << "(" << sepBy "," (map show os) << ")") ps))
        << match def with 
             | None => empty
             | Some def => indent "  " ("| _ => " << show (fst def) <<  "(" << sepBy "," (map show (snd def)))
           end
    end }.
  
  Definition showBlock (l : label) (b : block) : showM :=
    show l << "(" << sepBy "," (map show b.(b_args)) << "):"
    << indent "  " (sepBy chr_newline (map show b.(b_insns)))
    << indent "  " (chr_newline << show b.(b_term)).
    
  Global Instance Show_block : Show block :=
  { show := fun b => showBlock "_" b }.

  Fixpoint count_to {T} (f : nat -> T) (n : nat) : list T :=
    match n with
      | 0 => nil
      | S n => f n :: count_to f n 
    end.

  Global Instance Show_function : Show function :=
  { show := fun f =>
    let ks := 
      count_to (fun x => let c : cont := inl x in show c) f.(f_conts)
    in
    show f.(f_name) << "(" << match ks with
                                | nil => empty
                                | _ :: _ => sepBy "," nil << ";" 
                              end << sepBy "," (map show f.(f_args)) << "):"
    << indent "  " match Maps.lookup f.(f_entry) f.(f_body) with
                     | None => "<ERROR: couldn't find entry block>"
                     | Some b => showBlock f.(f_entry) b
                   end 
    << indent "  " (let ls : list showM := map (fun x => let '(l,b) := x in
      if eq_dec l f.(f_entry) then empty
      else
        chr_newline << showBlock l b) f.(f_body) in
    iter_show ls) }.

  Global Instance Show_program : Show program :=
  { show := fun p =>
    iter_show (map (fun x => show x) p.(p_topdecl))
    << chr_newline << "main = " << show p.(p_entry) }.

End Printing.
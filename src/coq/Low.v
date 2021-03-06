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

Definition mop := CpsCommon.mop.

Inductive instr :=
| Primop_i : var -> primop -> list op -> instr
| Alloca_i : list (var * primtyp) -> instr
| Malloc_i : list (var * primtyp) -> instr
(* Load_i(var,type,offset,ptr) => var = *((type* )(ptr+offset)) *)
| Load_i : var -> primtyp -> Z -> op -> instr
(* Store_i(type,value,offset,ptr) => *(ptr+offset) = value *)
| Store_i : primtyp -> op -> Z -> op -> instr
| Bind_i : var -> mop -> list op -> instr.

(* A function can be called with a list of continuations that were either 
   passed as arguments (referred to by the index of the formal) or that 
   were bound locally (referred to by the label of the generated code block
   and a list of arguments, which may include the return value). *)
Definition cont : Type := (nat + label)%type.

Inductive term :=
| Halt_tm : op -> term
| Call_tm : var -> op -> list op -> list (cont * list op) -> term
(* Return to a passed-in continuation *)
| Cont_tm : cont -> list op -> list op -> term
| Switch_tm : op -> list (pattern * label * list op) -> option (label * list op) -> term.

Record block := mk_block {
  b_args : list var;
  b_scope : list var;
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
      | Struct_t ls => "<" << sepBy "," (List.map show_primtyp ls) << ">"
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
      | Primop_i v p os => show v << " = " << show p << "(" << sepBy ", " (List.map show os) << ")"
      | Alloca_i vs => "[" << sepBy "," (List.map (fun x => show (fst x)) vs) <<
        "] = alloc(" << sepBy "," (List.map (fun x => show (snd x)) vs) << ")"
      | Malloc_i vs => "[" << sepBy "," (List.map (fun x => show (fst x)) vs) <<
        "] = malloc(" << sepBy "," (List.map (fun x => show (snd x)) vs) << ")"
      | Load_i x t d v => show x << " = load " << show t << " from " << show v << " + " << show d
      | Store_i t o d v => 
        "store " << show o << "@" << show t << " into " << show v << " + " << show d
      | Bind_i x m os =>
        show x << " = " << show m << "(" << sepBy ", " (List.map show os) << ")"
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
        show v << " = " << show fn << "(" << sepBy "," (List.map show args) << ") return ["
        << sepBy "," (List.map (fun k => let '(k,args) := k in
          show k << "(" << show args << ")") ks) << "]"
      | Cont_tm k locals args => "return " << show k << "(" 
        << sepBy "," (List.map show locals) << "; "
        << sepBy "," (List.map show args) << ")"
      | Switch_tm o ps def =>
        "switch " << show o 
        << indent "  " (chr_newline << sepBy chr_newline (List.map (fun plos => let '(p,l,os) := plos in
          "| " << show p << " => " << show l << "(" << sepBy "," (List.map show os) << ")") ps))
        << match def with 
             | None => empty
             | Some def => indent "  " ("| _ => " << show (fst def) <<  "(" << sepBy "," (List.map show (snd def)))
           end
    end }.
  
  Definition showBlock (l : label) (b : block) : showM :=
    l << "(inscope: " << sepBy ", " (List.map show b.(b_scope)) << "; args: "
    << sepBy ", " (List.map show b.(b_args)) << "):"
    << match b.(b_insns) with
         | nil => empty
         | _ => indent "  " (chr_newline << sepBy chr_newline (List.map show b.(b_insns)))
       end
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
                                | _ :: _ => sepBy "," ks << ";" 
                              end << sepBy "," (List.map show f.(f_args)) << ") {"
    << chr_newline
    << match Maps.lookup f.(f_entry) f.(f_body) with
         | None => "<ERROR: couldn't find entry block>"
         | Some b => showBlock f.(f_entry) b
       end 
    << let ls : list showM := map (fun x => let '(l,b) := x in
      if eq_dec l f.(f_entry) then empty
      else
        chr_newline << (showBlock l b)) f.(f_body) in
    iter_show ls
    << chr_newline << "}" << chr_newline }.

  Global Instance Show_program : Show program :=
  { show := fun p =>
    iter_show (List.map (fun x => chr_newline << show x) p.(p_topdecl))
    << chr_newline << "main = " << show p.(p_entry) }.

  Definition string_of_program (p : program) : string := runShow (show p) "".

End Printing.
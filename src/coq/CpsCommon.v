Require Import CoqCompile.Env CoqCompile.Lambda.
Require Import BinNums List.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

(** Operands are "small" values (fit into a register) and include variables, 
    zero-arity constructors (e.g., true, false, nil) and integers. *)
Inductive op : Type := 
| Var_o : var -> op
| Con_o : Lambda.constructor -> op
| Int_o : Z -> op
| InitWorld_o : op. (** this should be used only once **)

(** We compile pattern matching into simple C-like switch expressions, where
   you can only match an operand against a tag, which is either an integer
   or symbolic constructor tag. *)
Inductive pattern : Type := 
| Int_p : Z -> pattern
| Con_p : Lambda.constructor -> pattern.

(** We have a bunch of primitive operations on values *)
Inductive primop : Type := 
(* comparisons/tests *) 
| Eq_p     (* operand equality *)
| Neq_p    (* operand inequality *)
| Lt_p     (* integer less than *)
| Lte_p    (* integer ltess than or equal *)
| Ptr_p    (* is the value a pointer?  used to distinguish nullary constructors *)
(* arithmetic *)
| Plus_p   (* we don't include division as it's partial *)
| Minus_p 
| Times_p
(* build tuple and projection from a tuple *)
| MkTuple_p (* mkTuple_p [v1;...;vn] builds a record of n words and initializes it 
               with the values v1,...,vn. *)
| Proj_p.   (* Proj_p [Int_o i;v] projects the ith component of the tuple referenced
               by v, using zero-based indexing. *)

(** Monadic operations **)
Inductive mop : Type := 
| PrintChar_m : mop
| PrintCharF_m : mop
| Read_m : mop.

Section sanity.
  Definition primop_sane (p : primop) (ls : list op) : bool :=
    match p with
      | Eq_p | Neq_p | Lt_p | Lte_p
      | Plus_p | Minus_p | Times_p
      | Proj_p => match ls with
                    | _ :: _ :: nil => true
                    | _ => false
                  end
      | Ptr_p => match ls with
                   | _ :: nil => true
                   | _ => false
                 end
      | MkTuple_p => true
    end.

  Definition mop_sane (m : mop) (ls : list op) : bool :=
    match m with 
      | PrintChar_m => eq_dec 2 (List.length ls)
      | PrintCharF_m => eq_dec 10 (List.length ls)
      | Read_m => eq_dec 1 (List.length ls)
    end.

End sanity.

Section decidables.
  Require Import ExtLib.Core.RelDec.
  Require Import ExtLib.Core.ZDecidables.
  Require Import ExtLib.Core.PosDecidables.
  Require Import ExtLib.Data.Strings.
  Require Import ExtLib.Tactics.Consider.

  Global Instance RelDec_primop_eq : RelDec (@eq primop) := 
  { rel_dec := fun x y =>
    match x , y with
      | Eq_p , Eq_p 
      | Neq_p , Neq_p
      | Lt_p , Lt_p
      | Lte_p , Lte_p
      | Ptr_p , Ptr_p
      | Plus_p , Plus_p
      | Minus_p , Minus_p
      | Times_p , Times_p
      | MkTuple_p , MkTuple_p 
      | Proj_p , Proj_p => true
      | _ , _ => false
    end }.

  Global Instance RelDecCorrect_primop_eq : RelDec_Correct RelDec_primop_eq.
  Proof.
    constructor; destruct x; destruct y; simpl rel_dec; split; simpl; intros; subst; try congruence.
  Qed.

  Global Instance RelDec_mop_eq : RelDec (@eq mop) :=
  { rel_dec l r := match l , r with
                     | PrintChar_m , PrintChar_m => true
                     | PrintCharF_m , PrintCharF_m => true
                     | Read_m , Read_m => true
                     | _ , _ => false
                   end }.

  Global Instance RelDecCorrect_mop_eq : RelDec_Correct RelDec_mop_eq.
  Proof.
    constructor. destruct x; destruct y; simpl in *; intuition; try congruence.
  Qed.

  Global Instance RelDec_op_eq : RelDec (@eq op) :=
  { rel_dec l r := match l , r with
                     | Var_o l , Var_o r => eq_dec l r
                     | Con_o l , Con_o r => eq_dec l r
                     | Int_o l , Int_o r => eq_dec l r
                     | InitWorld_o , InitWorld_o => true
                     | _ , _ => false
                   end }.

  Global Instance RelDecCorrect_op_eq : RelDec_Correct RelDec_op_eq.
  Proof.
    Opaque Env.RelDec_var_eq RelDec_zeq.
    constructor. destruct x; destruct y; simpl; unfold eq_dec; try congruence; 
    try rewrite rel_dec_correct; intuition try congruence.
    consider (string_dec c c0); intuition congruence.
    consider (string_dec c c0); intuition congruence.
    Transparent Env.RelDec_var_eq RelDec_zeq.
  Qed.

  Global Instance RelDec_pattern_eq : RelDec (@eq pattern) :=
  { rel_dec l r := match l , r with
                     | Int_p i , Int_p i' => eq_dec i i'
                     | Con_p c , Con_p c' => eq_dec c c'
                     | _ , _ => false
                   end }.

  Global Instance RelDecCorrect_pattern_eq : RelDec_Correct RelDec_pattern_eq.
  Proof.
    Opaque Env.RelDec_var_eq RelDec_zeq.
    constructor. destruct x ; destruct y ; simpl ; unfold eq_dec ; try congruence;
    try rewrite rel_dec_correct ; intuition try congruence.
    consider (string_dec c c0) ; intuition congruence.
    consider (string_dec c c0) ; intuition congruence.
    Transparent Env.RelDec_var_eq RelDec_zeq.
  Qed.
End decidables.

Section Printing.
  Require Import ExtLib.Programming.Show.
  Require Import Ascii.
  Import ShowNotation.
  Local Open Scope string_scope.
  Local Open Scope show_scope.

  Global Instance Show_mop : Show mop :=
  { show m := match m with 
                | PrintChar_m => "PrintChar"
                | PrintCharF_m => "PrintCharF"
                | Read_m => "Read"
              end }.
    
  Global Instance Show_op : Show op :=
  { show o :=
    match o with 
      | Var_o x => show x
      | Con_o c => "Con(" << show c << ")"
      | Int_o i => show i
      | InitWorld_o => "<init-world>"
    end }.
  Global Instance Show_pat : Show pattern :=
  { show p :=
    match p with 
      | Int_p i => show i
      | Con_p c => show c
    end }.
  Global Instance Show_primop : Show primop :=
  { show p := 
    match p with 
      | Eq_p => "eq?"
      | Neq_p => "neq?"
      | Lt_p => "lt?"
      | Lte_p => "lte?"
      | Ptr_p => "ptr?"
      | Plus_p => "+"
      | Minus_p => "-"
      | Times_p => "*"
      | Proj_p => "#"
      | MkTuple_p => "mkTuple"
    end }.
End Printing.
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
Require Import ExtLib.Tactics.Consider.


Set Implicit Arguments.
Set Strict Implicit.

(** Defines CPS language datatype, pretty printer, and conversion from Lambda.exp
    to the CPS language.
*)
Module CPS.
  Import MonadNotation. 
  Local Open Scope monad_scope.
  Definition constructor := Lambda.constructor.
  Definition env_t := Lambda.env_t.

  (** Operands are "small" values (fit into a register) and include variables, 
      zero-arity constructors (e.g., true, false, nil) and integers. *)
  Inductive op : Type := 
  | Var_o : var -> op
  | Con_o : constructor -> op
  | Int_o : Z -> op.

  (** We compile pattern matching into simple C-like switch expressions, where
      you can only match an operand against a tag, which is either an integer
      or symbolic constructor tag. *)
  Inductive pattern : Type := 
  | Int_p : Z -> pattern
  | Con_p : constructor -> pattern.

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

  (** CPS are in general a sequence of let-bindings that either terminate with 
      a function application, or else fork using a switch into a tree of nested
      CPS expressions.  *)
  Inductive exp : Type := 
  | App_e : op -> list op -> exp
  | Let_e : decl -> exp -> exp
    (** Switch is only used on small integer values and unlike Match, doesn't do any
        pattern matching.  The optional expression at the end is a default in case
        none of the patterns matches the value. *)
  | Switch_e : op -> list (pattern * exp) -> option exp -> exp
  | Halt_e : op -> exp
  with decl : Type := 
    (** let x := v *)
  | Op_d : var -> op -> decl
    (** let x := p(v1,...,vn) *)
  | Prim_d : var -> primop -> list op -> decl
    (** let f := fun (x1,...,xn) => e *)
  | Fn_d : var -> list var -> exp -> decl
    (** let rec [d1;d2;...;dn].  Note that this is more general than we really need.
        What we need is letrec over both functions and over tuples (to support cyclic
        construction of data structures needed for recursive closures.)  In general,
        we will not have nested [Rec_d] declarations, and the nested declarations
        will either be a [Fn_d] or else a [Prim_d _ MkTuple_p]. *)
  | Rec_d : list decl -> decl.

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
    constructor; destruct x; destruct y; simpl rel_dec; split; intros; subst; try congruence.
  Qed.

  Global Instance RelDec_op_eq : RelDec (@eq op) :=
  { rel_dec l r := match l , r with
                     | Var_o l , Var_o r => eq_dec l r
                     | Con_o l , Con_o r => eq_dec l r
                     | Int_o l , Int_o r => eq_dec l r
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

  (** Simplify a switch that only has one branch. *)
  Definition switch_e (v:op) (arms: list (pattern * exp)) (def:option exp) := 
    match arms, def with 
      | (p,e)::nil, None => e
      | _, _ => Switch_e v arms def
    end.

  Section Printing.
  (** Pretty printing CPS expressions *)
    Require Import ExtLib.Programming.Show.
    Require Import Ascii.
    Import ShowNotation.
    Local Open Scope string_scope.
    Local Open Scope show_scope.

    Fixpoint spaces (n:nat) : showM :=
      match n with
        | 0 => empty
        | S n => " "%char << spaces n
      end.

    Global Instance Show_positive : Show positive :=
      { show p := show (Pos.to_nat p) }.

    Global Instance Show_Z : Show Z :=
      { show x :=
        match x with 
          | Z0 => "0"%char
          | Zpos p => show p
          | Zneg p => "-"%char << show p
        end }.
    Global Instance Show_op : Show op :=
      { show o :=
        match o with 
          | Var_o x => show x
          | Con_o c => "Con(" << show c << ")"
          | Int_o i => show i
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

    Require Import ExtLib.Data.Char.
    
    Fixpoint emitexp (e:exp) : showM :=
      match e with 
        | App_e v vs => show v << "(" << sepBy " " (map show vs) << ")"
        | Let_e d e =>
          "let " << indent "  " (emitdecl false d) << "in " << indent "  " (emitexp e)
        | Switch_e v arms def => 
          "switch " << empty (*show v*) << " with" << empty (*
          indent "  " (
            iterM (fun (p: pattern * exp) => 
              chr_newline << "| " << show (fst p) << " => " << emitexp (snd p)) arms
            << match def with 
                 | None => empty
                 | Some e => chr_newline << "| _ => " << emitexp e
               end) *)
          << chr_newline << "end"
        | Halt_e o => "HALT " << show o
      end
    with emitdecl (inrec:bool) (d:decl) : showM := 
      let emit_sep : showM := if inrec then " and" else " in" in 
        match d with 
          | Op_d x v => 
            show x << " = " << show v << emit_sep 
          | Prim_d x p vs => 
            show x << " = " << show p << "(" << sepBy " " (map show vs) << ")" << emit_sep 
          | Fn_d f xs e => 
            show f << "(" << sepBy (", " : showM) (map show xs) << ") = " << indent "  " (emitexp e) << emit_sep 
          | Rec_d ds => 
          "rec "<< sepBy chr_newline (map (emitdecl true) ds)
        end.

    Global Instance Show_exp : Show exp := emitexp.
    Global Instance Show_decl : Show decl := emitdecl false.

    Definition exp2string (e:exp) : string := 
      @runShow (string -> string) _ (show e) "".
    
  End Printing.

End CPS.

Export Env.

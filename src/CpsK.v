Require Import CoqCompile.Lambda CoqCompile.Env CoqCompile.CpsCommon.
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

(** This file explores a design point where we make continuations second class.
 ** We determined several things:
 ** 1) Second-class continuations are a little more verbose to code with
 **    because you have to have separate binders and application
 ** 2) Second-class continuations make it difficult to represent double-barrel
 **    Cps and other, non-standard uses of continuations
 ** 3) There isn't really a semantic distinction between continuations and
 **    functions which makes it difficult to understand when an optimization
 **    is correct.
 ** Point 2) might still be possible in this representation, but it seems a
 ** little strange.
 **)

(** Defines CPS language datatype, pretty printer, and conversion from Lambda.exp
    to the CPS language.
*)
Module CPSK.
  Import MonadNotation. 
  Local Open Scope monad_scope.
  Definition constructor := Lambda.constructor.
  Definition env_t := Lambda.env_t.

  Inductive cont : Type := K : string -> positive -> cont.

  Definition wrapCont (s : string) : cont := K s 1%positive.

  (** CPS are in general a sequence of let-bindings that either terminate with 
      a function application, or else fork using a switch into a tree of nested
      CPS expressions.  *)
  Inductive exp : Type := 
  | App_e : op -> list cont -> list op -> exp
  | Let_e : decl -> exp -> exp
  | Letrec_e : list decl -> exp -> exp
    (** Switch is only used on small integer values and unlike Match, doesn't do any
        pattern matching.  The optional expression at the end is a default in case
        none of the patterns matches the value. *)
  | Switch_e : op -> list (pattern * exp) -> option exp -> exp
  | Halt_e : op -> op -> exp

  | AppK_e : cont -> list op -> exp
  | LetK_e : list (cont * list var * exp) -> exp -> exp
  with decl : Type := 
    (** let x := v *)
  | Op_d : var -> op -> decl
    (** let x := p(v1,...,vn) *)
  | Prim_d : var -> primop -> list op -> decl
    (** let f := fun (x1,...,xn) => e *)
  | Fn_d : var -> list cont -> list var -> exp -> decl
  | Bind_d : var -> var -> mop -> list op -> decl.

  Global Instance RelDec_cont_eq : RelDec (@eq cont) :=
  { rel_dec l r := match l , r with
                     | K s1 i1 , K s2 i2 => eq_dec s1 s2 && eq_dec i1 i2
                   end }.

  Global Instance RelDecCorrect_cont_eq : RelDec_Correct RelDec_cont_eq.
  Proof.
    constructor. destruct x; destruct y; simpl.
    change (p =? p0)%positive with (rel_dec (equ := eq) p p0).
    consider (string_dec s s0 && rel_dec (equ := eq) p p0); intuition; subst; auto;
    inversion H; auto.
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

    Global Instance Show_cont : Show cont :=
      { show c :=
        match c with
          | K x i => "%" << x << show i 
        end }.

    Require Import ExtLib.Data.Char.
    
    Fixpoint emitexp (e:exp) : showM :=
      match e with 
        | AppK_e k vs => "return " << show k << "(" << sepBy ", " (map show vs) << ")"
        | LetK_e ks e =>
          let emitKd (kd : cont * list var * exp) : showM :=
            let '(k, xs, b) := kd in 
            show k << "(" << sepBy ", " (map show xs) << ") := " << emitexp b
          in
          "letK " << indent "and  " (sepBy chr_newline (map emitKd ks)) << chr_newline
          << "in " << emitexp e
        | App_e v ks vs => show v << "(" << sepBy "," (map show ks) << "; " << sepBy ", " (map show vs) << ")"
        | Let_e d e =>
          "let " << indent "  " (emitdecl d) << " in " << indent "  " (emitexp e)
        | Letrec_e ds e => 
          "let rec " << indent "    and " (sepBy chr_newline (map emitdecl ds)) <<
          chr_newline << "in " << emitexp e 
        | Switch_e v arms def => 
          "switch " << empty (*show v*) << " with" << 
          indent "  " (
            sepBy empty (map (fun (p: pattern * exp) => 
              chr_newline << "| " << show (fst p) << " => " << emitexp (snd p)) arms)
            << match def with 
                 | None => empty
                 | Some e => chr_newline << "| _ => " << emitexp e
               end)
          << chr_newline << "end"
        | Halt_e o w => "HALT " << show o << " " << show w 
      end
    with emitdecl (d:decl) : showM := 
      match d with 
        | Op_d x v => 
          show x << " = " << show v
        | Prim_d x p vs => 
          show x << " = " << show p << "(" << sepBy " " (map show vs) << ")"
        | Fn_d f k xs e => 
          show f << "(" << sepBy "," (map show k) << "; " << sepBy (", " : showM) (map show xs) << ") = " << indent "  " (emitexp e)
        | Bind_d x w mop args =>
          show x << "[" << show w << "] <- " << show mop << "(" << sepBy " " (map show args) << ")"
      end.

    Global Instance Show_exp : Show exp := emitexp.
    Global Instance Show_decl : Show decl := emitdecl.

    Definition exp2string (e:exp) : string := to_string e.
    
  End Printing.
End CPSK.

Export Env.
Export CpsCommon.
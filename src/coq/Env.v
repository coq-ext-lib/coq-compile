Require Import List BinPos String.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.CmpDec.
Require Import ExtLib.Core.PosDecidables.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Section with_map.
  Variable map : Type -> Type.
  Variable K : Type.
  Context {Map_map : DMap K map}.

  Fixpoint add_all {A} (m : map A) (xs:list K) (vs:list A) : map A :=
    match xs, vs with
      | x::xs, v::vs => add x v (add_all m xs vs)
      | _, _ => m
    end.
End with_map.

Inductive var := 
| Anon_v : positive -> var
| Named_v : string -> option positive -> var.

Definition mkVar (v : option string) (n : positive) : var :=
  match v with
    | None => Anon_v n
    | Some s => Named_v s (Some n)
  end.

Definition wrapVar (v : string) : var :=
  Named_v v None.

Global Instance RelDec_var_eq : RelDec (@eq var) :=
{ rel_dec x y :=
    match x , y with
      | Anon_v x , Anon_v y => eq_dec x y
      | Named_v x xi , Named_v y yi =>
        if eq_dec x y then eq_dec xi yi else false
      | _ , _ => false
    end }.

Global Instance RelDec_Correct_var_eq : RelDec_Correct RelDec_var_eq.
Proof.
  Opaque RelDec_peq.
  constructor.  destruct x; destruct y; intros; simpl in *; intuition; try congruence.
  consider (eq_dec p p0); intros; subst; auto.
  inversion H; clear H; subst.
  consider (eq_dec p0 p0); auto.
  consider (string_dec s s0); intros; subst.
  destruct o; destruct o0; try congruence.
  consider (eq_dec p p0); intros; subst; auto.
  inversion H; clear H; subst.
  consider (string_dec s0 s0); try congruence; intros.
  destruct o0; auto. consider (eq_dec p p); auto.
Qed.

Global Instance CmpDec_positive : CmpDec (@eq positive) Pos.lt :=
{ cmp_dec := Pos.compare }.

Section hiding_notation.
  Import ShowNotation.
  Require Import Ascii.
  Local Open Scope show.

  Global Instance Show_var : Show var :=
    fun x =>
      match x with
        | Anon_v p => "$"%char << show p
        | Named_v n None => n
        | Named_v n (Some p) => n << "_"%char << show p
      end.
End hiding_notation.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Inductive mem (T : Type) : list T -> T -> Type :=
| memH : forall t ls, mem (t :: ls) t
| memS : forall t t' ls, mem ls t -> mem (t' :: ls) t.

Arguments memH {_ _ _}.
Arguments memS {_ _ _ _} _.


Class OptEquation (T : Type) : Type := OptRewrite
{ env   : list Type
; left  : (forall {t}, mem env t -> t) -> T
; right : (forall {t}, mem env t -> t) -> T
; proof : forall g, left g = right g
}.

(** Example rewrite **)
Require Import List.

Notation "g # 1" := (g _ memH) (at level 0).
Notation "g # 2" := (g _ (memS memH)) (at level 0).
Notation "g # 3" := (g _ (memS (memS memH))) (at level 0).

Instance Eqn_hd (T : Type) : OptEquation T :=
{ env   := T :: list T :: T :: nil 
; left  := fun g => hd (g#3) (cons (g#1) (g#2))
; right := fun g => g T memH
; proof := _
}.
reflexivity.
Qed.

Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Class OptEquation (T : Type) : Type := OptRewrite
{ env   : list Type
; left  : (forall n, nth n env unit) -> T
; right : (forall n, nth n env unit) -> T
; proof : forall g, left g = right g
}.

(** Example rewrite **)
Instance Eqn_hd (T : Type) : OptEquation T :=
{ env   := T :: list T :: T :: nil 
; left  := fun g => hd (g 2) (cons (g 0) (g 1))
; right := fun g => g 0
}.
reflexivity.
Defined.

Instance Eqn_uncurry (A B : Type) (T : Type) : OptEquation T :=
{ env   := (A -> B -> T) :: A :: B :: nil
; left  := fun g => (g 0) (g 1) (g 2)
; right := fun g => (fun x => (g 0) (fst x) (snd x)) (g 1, g 2)
}.
reflexivity.
Defined.

(**
Extraction Language Scheme.
Recursive Extraction Eqn_hd.
**)
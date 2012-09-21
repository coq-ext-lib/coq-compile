Require Import List.
Require Import ExtLib.FMaps.FMaps.

Set Implicit Arguments.
Set Strict Implicit.

Section with_map.
  Variable map : Type -> Type.
  Variable K : Type.
  Context {Map_map : Map K map}.

  Fixpoint add_all {A} (m : map A) (xs:list K) (vs:list A) : map A :=
    match xs, vs with
      | x::xs, v::vs => add x v (add_all m xs vs)
      | _, _ => m
    end.
End with_map.
Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => n * fact n'
  end.

Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.

Import ShowNotation.
Local Open Scope show_scope.

Definition main : IO unit :=
  runShow ((show_exact "3! = ") << (show (fact 3))).

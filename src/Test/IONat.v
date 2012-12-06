Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.

Definition main : IO unit :=
  runShow (show 1).

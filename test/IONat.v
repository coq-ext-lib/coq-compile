Require Import CoqIO.IO.
Require Import ExtLib.Programming.Show.

Definition main : IO unit :=
  runShow (M := ShowScheme_Std StdOut) (show 1).

Require Import CoqIO.IO.
Require Import ExtLib.Programming.Show.

Definition main : IO unit :=
  runShow (M := ShowScheme_IO StdOut) (show 1).

Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.

Import ShowNotation.
Local Open Scope show_scope.

Definition main : IO unit :=
  runShow (show_exact "Hello world!" << Char.chr_newline).

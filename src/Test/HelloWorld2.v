Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.

Import ShowNotation.
Local Open Scope show_scope.

Definition main : IO unit :=
  runShow ((show_exact "H!") << (show Char.chr_newline)).

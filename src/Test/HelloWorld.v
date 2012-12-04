Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.


Definition main : IO unit :=
  runShow (show_exact "Hello World!").
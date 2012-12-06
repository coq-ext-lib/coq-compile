Require Import CoqCompile.IO.
Require Import ExtLib.Programming.Show.
Require Import Ascii.

Definition main : IO unit :=
  IO_printChar "*"%char.
(*  runShow (show_exact "Hello World!").*)
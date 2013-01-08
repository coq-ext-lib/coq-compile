Require Import CoqIO.IO.
Require Import ExtLib.Programming.Show.

Import ShowNotation.
Local Open Scope show_scope.

Definition main : IO unit :=
  runShow (M := ShowScheme_IO StdOut) 
          (show_exact "Hello world!" << Char.chr_newline).

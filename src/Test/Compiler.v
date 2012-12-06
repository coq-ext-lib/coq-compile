Require Import CoqCompile.Compile.
Require Import LLVM.
Require Import Lambda.

Definition result : Compile.m LLVM.module :=
  Compile.topCompile 8 Compile.Opt.O0 true (LambdaNotation.gen LambdaNotation.e8).


Extraction Language Scheme.
Recursive Extraction result.
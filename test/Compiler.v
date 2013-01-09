Require Import CoqCompile.Compile.
Require Import CoqCompile.CompileDriver.
Require Import CoqCompile.Compile.
Require Import CoqCompile.Lambda.
Require Import CoqIO.IO.
Require Import ExtLib.Programming.Show.

Definition prg := 
  Eval vm_compute in (LambdaNotation.gen LambdaNotation.e8).

Definition main := 
  compile_lam 8 opt0 true Compile.LLVM_stop false (IO_printCharF StdOut) prg. 

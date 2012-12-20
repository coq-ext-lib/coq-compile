Require Import CoqCompile.Compile.
Require Import LLVM.
Require Import Lambda.
Require Import String.
Require Import ExtLib.Programming.Show.

Definition result (* : Compile.m LLVM.module*) :=
  match 
    Compile.runM (Compile.topCompile 8 Compile.Opt.O0 true (LambdaNotation.gen LambdaNotation.e8) Compile.LLVM_stop false)
    with
    | (inr m, _) => to_string m
    | _ => "error"%string
  end.

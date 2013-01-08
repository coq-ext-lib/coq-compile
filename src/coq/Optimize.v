Require Import List.
Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable exp : Type.
  Variable m : Type -> Type.

  Definition optimization : Type := exp -> m exp.
  
  Context {Monad_m : Monad m}.

  Fixpoint optSeq (os : list optimization) : optimization :=
    match os with
      | nil => fun x => ret x
      | o :: os => fun x => bind (o x) (optSeq os)
    end.
  
  Fixpoint optRepeat (n : nat) (o : optimization) : optimization :=
    match n with
      | 0 => o
      | S n => fun x => bind (o x) (optRepeat n o)
    end.
End parametric.


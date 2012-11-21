Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Module Optimize.

  Section parametric.
    Variable exp : Type.


    Definition optimization : Type := exp -> exp.
    
    Fixpoint optSeq (os : list optimization) : optimization :=
      match os with
        | nil => fun x => x
        | o :: os => fun x => optSeq os (o x)
      end.
    
    Fixpoint optRepeat (n : nat) (o : optimization) : optimization :=
      match n with
        | 0 => o
        | S n => fun x => optRepeat n o (o x)
      end.
  End parametric.

End Optimize.

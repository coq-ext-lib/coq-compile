Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadTrace (T : Type) (m : Type -> Type) : Type :=
{ mlog : T -> m unit
; mtrace : forall A, T -> A -> m A
}.

Require Import ExtLib.Data.Monads.StateMonad.

Section traceT.
  Variables (T : Type) (m : Type -> Type).

  Record traceT (A : Type) := mkTraceT
  { runTraceT : stateT (list T) m A }.

  Definition traceTraceT {A} (c : traceT A) : m (A * list T) :=
    runStateT (runTraceT c) nil.

  Context {Monad_m : Monad m}.

  Global Instance Monad_traceT : Monad traceT :=
  { ret := fun _ x => mkTraceT (ret x)
  ; bind := fun _ c _ f => mkTraceT (bind (runTraceT c) (fun x => runTraceT (f x)))
  }.

  Global Instance MonadT_traceT : MonadT traceT m :=
  { lift := fun _ c => mkTraceT (lift c) }.

  Global Instance MonadReader_traceT {S} {MR : MonadReader S m} 
    : MonadReader S traceT :=
  { ask := lift ask
  ; local := fun f _ c => mkTraceT (local f (runTraceT c))
  }.

  Global Instance MonadState_traceT {S} {MS : MonadState S m} 
    : MonadState S traceT :=
  { get := lift get
  ; put := fun v => mkTraceT (put v)
  }.

  Global Instance MonadExc_traceT {S} {MS : MonadExc S m} 
    : MonadExc S traceT :=
  { raise := fun _ e => lift (raise e)
  ; catch := fun _ c e => 
    mkTraceT (catch (runTraceT c) (fun x => runTraceT (e x)))
  }.

  Global Instance MonadZero_traceT {MS : MonadZero m} 
    : MonadZero traceT :=
  { mzero := fun _ => lift mzero }.

End traceT.

(*
Inductive TMsg : Type := 
| Msg : forall {T}, Show T -> T -> TMsg
| Value : forall {T}, T -> TMsg.

Section traced.
  Class Identifier (U T : Type) (f : T) : Type :=
  { identFor : U }.

  Variable T : Type.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MT : MonadTrace T m}.

  Definition ftrace {U : Type} (f : m U) {Id : Identifier T f} : m U :=
    bind (mtrace identFor f) (fun _ => f).

  Definition ftrace1 {A U : Type} (f : A -> m U) {Id : Identifier T f} (a : A) : m U :=
    bind (mtrace identFor f) (fun _ => f a).

  Definition ftrace2 {A B U : Type} (f : A -> B -> m U) {Id : Identifier T f} (a : A) (b : B) : m U :=
    bind (mtrace identFor f) (fun _ => f a b).

  Definition ftrace3 {A B C U : Type} (f : A -> B -> C -> m U) {Id : Identifier T f} (a : A) (b : B) (c : C) : m U :=
    bind (mtrace identFor f) (fun _ => f a b c).

  Definition ftrace4 {A B C D U : Type} (f : A -> B -> C -> D -> m U) {Id : Identifier T f} (a : A) (b : B) (c : C) (d : D) : m U :=
    bind (mtrace identFor f) (fun _ => f a b c d).

  Definition ftrace5 {A B C D E U : Type} (f : A -> B -> C -> D -> E -> m U) {Id : Identifier T f} (a : A) (b : B) (c : C) (d : D) (e : E) : m U :=
    bind (mtrace identFor f) (fun _ => f a b c d e).

End traced.
*)
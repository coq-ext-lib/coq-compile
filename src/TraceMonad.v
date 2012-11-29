Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadTrace (T : Type) (m : Type -> Type) : Type :=
{ mlog : T -> m unit }.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.EitherMonad.

Section traceT.
  Variables (T : Type) (m : Type -> Type).

  Import MonadNotation.
  Local Open Scope monad_scope.

  Record traceT (A : Type) := mkTraceT
  { runTraceT : stateT (list T) m A }.

  Definition traceTraceT {A} (c : traceT A) : m (A * list T) :=
    runStateT (runTraceT c) nil.

  Context {Monad_m : Monad m}.

  Global Instance MonadTrace_traceT : MonadTrace T traceT :=
  { mlog := fun x => mkTraceT (modify (fun y => x::y)%list ;; ret tt) }.

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
 
  Global Instance MonadWriter_traceT {T M} {MR: @MonadWriter T M m}
    : @MonadWriter T M traceT :=
  { tell := fun x => lift (tell x)
  ; listen := fun _ x => mkTraceT (listen (runTraceT x))
  ; pass := fun _ x => mkTraceT (pass (runTraceT x))
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

Section instances.
  Variables (T : Type) (m : Type -> Type).

  Global Instance MonadTrace_readerT {T S} {MT : MonadTrace T m}
    : MonadTrace T (readerT S m) :=
  { mlog := fun x => lift (mlog x) }.

  Global Instance MonadTrace_writerT {T S} {M : Monoid.Monoid S} {MT : MonadTrace T m} (Mo : Monad m)
    : MonadTrace T (writerT M m) :=
  { mlog := fun x => @lift (writerT M m) m (MonadT_writerT M Mo) _ (mlog x) }.

  Global Instance MonadTrace_stateT {T S} {MT : MonadTrace T m} {Mo : Monad m}
    : MonadTrace T (stateT S m) :=
  { mlog := fun x => lift (mlog x) }.

  Global Instance MonadTrace_eitherT {T S} {MT : MonadTrace T m} {Mo : Monad m}
    : MonadTrace T (eitherT S m) :=
  { mlog := fun x => lift (mlog x) }.

End instances.

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
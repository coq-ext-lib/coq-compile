Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Maximal Implicit Arguments.

Class MonadTrace (T : Type) (m : Type -> Type) : Type :=
{ mlog : T -> m unit }.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.FuelMonad.

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

  Global Instance MonadFix_traceT {MF : MonadFix m}
    : MonadFix traceT :=
  { mfix := fun _ _ r x => mkTraceT (mfix (fun g y => runTraceT (r (fun z => mkTraceT (g z)) y)) x) }.

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
  
  Global Instance MonadTrace_GFixT {T} {MT : MonadTrace T m} {Mo : Monad m}
    : MonadTrace T (GFixT m) :=
  { mlog := fun x => lift (mlog x) }.

End instances.

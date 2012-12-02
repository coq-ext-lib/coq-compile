Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Core.RelDec.

Import CpsK.CPSK.

Section AbstractDomain.
  
  Class AbsTime (C : Type) : Type :=
  { ED :> RelDec (@eq C)
    (** What does this have? 
     ** - there should be a way to refine a context to include some pure fact, e.g.
     **   "assume this equality"
     ** - there should also be a way to record a stack of call sites for context
     **   analysis
     **)
  }.
  
  Class AbsDomain (Domain Value Context ProgramPoint : Type) : Type :=
  { lookup  : Context -> ProgramPoint -> Domain -> Value
  ; update  : Context -> ProgramPoint -> Value -> Domain -> Domain
  ; joinA   : Value -> Value -> Value
  ; bottomA : Value (** this means empty, i.e. never has a value **)
  ; topA    : Value (** this means anything of any type **)
  ; dom_leq   : Domain -> Domain -> bool
  }.

  Class IntValue (V : Type) : Type :=
  { injInt : option BinNums.Z -> V
  ; plusA  : V -> V -> V
  ; minusA : V -> V -> V
  ; timesA : V -> V -> V
  ; eqA    : V -> V -> option bool
  ; ltA    : V -> V -> option bool
  }.

  Class CtorValue (V : Type) (Ctor : Type) : Type :=
  { injCtor : Ctor -> V
  ; isPtrA  : V -> option bool
  ; ceqA    : V -> V -> option bool
  }.

  Class BoolValue (V : Type) : Type :=
  { injBool : option bool -> V
  ; may : V -> bool -> bool
  ; must : V -> bool -> bool
  ; orA : V -> V -> V
  }.

  Class FnValue (V C D : Type) : Type :=
  { injFn  : C -> list cont -> list var -> exp -> V 
  ; applyA : forall {m} {_ : Monad m}, (C -> D -> exp -> m D%type) -> D -> V -> list V -> list V -> m D%type
  }.

  Class TplValue (V : Type) : Type :=
  { injTuple : list V -> V
  ; projA    : V -> V -> V
  }.

End AbstractDomain.
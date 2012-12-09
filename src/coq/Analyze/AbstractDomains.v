Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Core.RelDec.
Require Import String.
Require Import CoqCompile.TraceMonad.

Import CpsK.CPSK.

Set Implicit Arguments.
Set Strict Implicit.

Section AbstractDomain.
  
  Variable C : Type.  (* Context *)
  Variable D : Type.  (* Domain *)
  Variable PP : Type. (* Program point, which in our case is just a var + cont name *)
  Variables V : Type. (* Sets of values *)

  Class AbsTime : Type :=
  { ED :> RelDec (@eq C)
    (** What does this have? 
     ** - there should be a way to refine a context to include some pure fact, e.g.
     **   "assume this equality"
     ** - there should also be a way to record a stack of call sites for context
     **   analysis
     **)
  ; enter : C -> PP -> C
  }.

  
  Class AbsDomain : Type :=
  { lookup  : C -> PP -> D -> V
  ; update  : C -> PP -> V -> D -> D
  ; joinA   : D -> D -> D
  ; bottomA : V (** this means empty, i.e. never has a value **)
  ; topA    : V (** this means anything of any type **)
  ; dom_leq : D -> D -> bool
  }.

  Class IntValue : Type :=
  { injInt : option BinNums.Z -> V
  ; plusA  : V -> V -> V
  ; minusA : V -> V -> V
  ; timesA : V -> V -> V
  ; eqA    : V -> V -> option bool
  ; ltA    : V -> V -> option bool
  }.

  Class CtorValue (Ctor : Type) : Type :=
  { injCtor : Ctor -> V
  ; isPtrA  : V -> option bool
  ; ceqA    : V -> V -> option bool
  }.

  Class BoolValue : Type :=
  { injBool : option bool -> V
  ; may : V -> bool -> bool
  ; must : V -> bool -> bool
  ; orA : V -> V -> V
  }.

  Class FnValue : Type :=
  { injFn  : C -> PP -> list cont -> list var -> exp -> V 
  ; applyA : forall {m} {_ : Monad m} {_ : MonadTrace string m} {_ : AbsTime}, 
    (C -> D -> exp -> m D%type) ->
    D -> V -> list V -> list V -> m D%type
  }.

  Class TplValue : Type :=
  { injTuple : D -> C -> var -> list V -> D
  ; projA    : D -> C -> V -> V -> V
  }.

End AbstractDomain.

Arguments bottomA {_ _ _ _ _}.
Arguments topA {_ _ _ _ _}.
Arguments joinA {_ _ _ _ _} _ _.

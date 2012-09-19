Require Import Lambda.
Import Lambda.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive atom :=
| VarAtom : var -> atom
| ConAtom : constructor -> atom
.

Inductive kon := VarKon : var -> kon.

Inductive
small :=
| ConSmall : constructor -> list atom -> small
| LamSmall : var -> var -> call -> small
| KonSmall : var -> call -> small
with
bind :=
| OneBind : var -> small -> bind
| RecBind : list (var * small) -> bind
with
call :=
| LetCall : bind -> call -> call
| AppCall : atom -> atom -> kon -> call
| KonCall : kon -> atom -> call
| MatchCall : atom -> list (pattern * call) -> call
| HaltCall : atom -> call
.

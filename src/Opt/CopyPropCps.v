Require Import Cps Lambda.
Require Import String List.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.FMaps.FMapAList.
Require Import CoqCompile.Env.

Set Implicit Arguments.
Set Strict Implicit.

Module CopyProp.
  Import CPS.
  Local Open Scope monad_scope.

  Section with_env.
    Variable env_t : Type -> Type.
    Context {M : Map var env_t}.

  (** Copy Propagation:  reduce all expressions of the form:

      match v with
      | x => e
      end

     into e[v/x].

     (Note that this is the only real way we have to encode: "let x = v in e")

     This assumes we don't capture variables.  There are at least two
     ways to deal with this problem:  ensure all variables are
     uniquely named so we don't have to worry about it;  alternatively,
     rename as we go.

     Or, we could use deBruijn indices but that introduces many problems
     later on.  For instance, we cannot use a global map from variable names
     to counts in the dead-code and inline passes below.  We would need
     some notion of "path" instead.
  *)
    Definition cprop_op (subst:env_t op) (v:op) : op :=
      match v with
        | Var_o x => match find x subst with | None => v | Some v' => v' end
        | _ => v
      end.

    Definition cprop_list (subst:env_t op) (vs:list op): list op :=
      List.map (cprop_op subst) vs.

    Fixpoint cprop (subst:env_t op) e : exp :=
      match e with
        | App_e v vs => App_e (cprop_op subst v) (cprop_list subst vs)
        | Let_e x c vs e => Let_e x c (cprop_list subst vs) (cprop subst e)
        | Match_e v ((Lambda.Var_p x,e)::nil) =>
          let v' := cprop_op subst v in cprop (add x v' subst) e
        | Match_e v arms =>
          Match_e (cprop_op subst v)
          (List.map (fun (arm:pattern*exp) => (fst arm, cprop subst (snd arm))) arms)
        | Letrec_e fs e =>
          Letrec_e
          (List.map (fun (fn:var*(list var*exp)) =>
            match fn with (f,(x,e)) => (f,(x,cprop subst e)) end) fs) (cprop subst e)
      end.

    Definition copyprop := cprop empty.
  End with_env.

(*
  Section TEST_COPYPROP.
    Import LambdaNotation.
    
    Eval compute in (cps2string (CPS (gen e1))).
    Open Local Scope string_scope.
    Set Printing Depth 100.

    Eval compute in (cps2string (copyprop (env_t := alist Lambda.var) (CPS (gen e1)))).
  End TEST_COPYPROP.
*)
End CopyProp.
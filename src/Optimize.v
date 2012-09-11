Require Import Lambda Cps.
Require Import String List.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad ExtLib.Monad.ContMonad.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Module Optimize.
  Import CPS.
  Definition initial_env {A} : var -> option A := fun x => None.
  Definition extend {A} (env:var -> option A) (x:var) (v:A) : var -> option A :=
    fun y => if string_dec y x then Some v else env y.
  
  Fixpoint substs {A} (xs:list var) (vs:list A) : var -> option A := 
    match xs, vs with 
      | x::xs, v::vs => extend (substs xs vs) x v
      | _, _ => initial_env
    end.
  
(** Copy Propagation:  reduce all expressions of the form:
   
   match v with 
   | x => e 
   end
   
   into e[v/x]. 
   
   Note that this assumes we don't capture variables.  Two
   ways to deal with this problem:  ensure all variables are
   uniquely named so we don't have to worry about it;  alternatively,
   rename as we go.  
*)
  Definition cprop_op (subst:var -> option op) (v:op) : op := 
    match v with 
      | Var_o x => match subst x with | None => v | Some v' => v' end
      | _ => v
    end.

  Definition cprop_list (subst:var -> option op) (vs:list op): list op := 
    List.map (cprop_op subst) vs.

  Fixpoint cprop (subst:var -> option op) e : exp := 
    match e with 
      | App_e v vs => App_e (cprop_op subst v) (cprop_list subst vs)
      | Let_e x c vs e => Let_e x c (cprop_list subst vs) (cprop subst e)
      | Match_e v ((Lambda.Var_p x,e)::nil) => 
        let v' := cprop_op subst v in 
          cprop (fun y => if string_dec x y then Some v' else subst y) e
      | Match_e v arms => 
        Match_e (cprop_op subst v) 
        (List.map (fun (arm:pattern*exp) => (fst arm, cprop subst (snd arm))) arms)
      | Letrec_e fs e => 
        Letrec_e 
        (List.map (fun (fn:var*(list var*exp)) => 
          match fn with (f,(x,e)) => 
            (f,(x,cprop subst e)) end) fs) (cprop subst e)
    end.

  Definition copyprop := cprop initial_env.

  Section TEST_COPYPROP.
    Import LambdaNotation.
    Eval compute in (cps2string (CPS (gen e1))).
    Eval compute in (cps2string (copyprop (CPS (gen e1)))).
  End TEST_COPYPROP.

  (** More match reduction:
     
     match C with | ... | C => e | ... end => e
     
     let x = C v1 ... vn in 
     ...
     match x with | ... | C x1 ... xn => e | ... end => e[vi/xi]
     
     This also has the variable capture problem.  In addition, the way
     it's coded makes it hard to prove termination.  Finally, the right
     way to do this is to fuse together the copy propagation with the
     reductions.  
     *)
  Fixpoint reduce (n:nat)(env:var -> option (constructor * list op)) (e:exp) : exp := 
    match n with 
      | 0 => e
      | S n => 
        let reduce_arm := fun (arm:pattern*exp) => (fst arm, reduce n env (snd arm)) in
          let find_arm := 
            fix find (c:constructor)(arms:list (pattern*exp)) : option (pattern*exp) := 
            match arms with 
              | nil => None 
              | (Lambda.Con_p c' xs,e)::rest => 
                if string_dec c c' then Some (Lambda.Con_p c' xs,e) else find c rest
              | (Lambda.Var_p x,e)::rest => Some (Lambda.Var_p x,e)
            end in 
            match e with 
              | Match_e (Var_o x) arms => 
                match env x with 
                  | Some (c,vs) => 
                    match find_arm c arms with 
                      | Some (Lambda.Con_p _ ys,ec) => 
                        reduce n env (cprop (substs ys vs) ec)
                      | Some (Lambda.Var_p y,ec) => 
                        reduce n env (cprop (substs (y::nil) ((Var_o x)::nil)) ec)
                      | _ => e
                    end
                  | None => Match_e (Var_o x) (List.map reduce_arm arms)
                end
              | Match_e (Con_o c) arms => 
                match find_arm c arms with 
                  | Some (Lambda.Con_p _ _,ec) => reduce n env ec
                  | _ => e
                end
              | Let_e x c vs e => Let_e x c vs (reduce n (extend env x (c,vs)) e)
              | Letrec_e fs e => 
                Letrec_e 
                (List.map (fun fn => 
                  match fn with 
                    | (f,(xs,e)) => (f,(xs,reduce n env e))
                  end) fs) (reduce n env e)
              | App_e v vs => App_e v vs
            end
    end.
  
  Definition optimize (fuel:nat) (e:exp) : exp := 
    reduce fuel initial_env (cprop initial_env e).

  Section TEST_OPTIMIZER.
    Import LambdaNotation.
    Eval compute in (cps2string (CPS (gen e6))).
    Eval compute in (cps2string (optimize 100 (CPS (gen e6)))).
  End TEST_OPTIMIZER.
End Optimize.
Require Import Cps Lambda.
Require Import String List.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.FMaps.FMapAList.
Require Import ExtLib.Decidables.Decidable.
Require Import CoqCompile.Opt.CopyPropCps.
Require Import CoqCompile.Env.

Set Implicit Arguments.
Set Strict Implicit.

Module MatchRed.
  Import CPS.

  Section with_env.
    Variable env_t : Type -> Type.
    Context {M : Map var env_t}.

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
    Fixpoint reduce (n:nat)(env:env_t (constructor * list op)) (e:exp) : exp :=
      match n with
        | 0 => e
        | S n =>
         (* specialize the match arm under the assumption that the
            pattern is now equal to x.  For instance, if we have:
         
            match x with 
            | Cons h t => ... match x with 
                              | Cons h1 t1 => e1
                              | Nil => e2
            | Nil => ... match x with 
                         | Cons h3 t3 => e3
                         | Nil => e4

            then we can reduce the inner matches if for each arm, we remember
            that (x = Cons h t) and (x = Nil) respectively. *)
          let reduce_arm (x:var) (arm:pattern*exp) : pattern * exp := 
            (fst arm, 
              match (fst arm) with 
                | Lambda.Con_p c nil =>
                  (* in this branch, substitute Con_o c for x *)
                  reduce n env (CopyProp.cprop (add x (Con_o c) empty) (snd arm))
                | Lambda.Con_p c xs =>
                  (* in this branch, treat x as bound to (c vs) *)
                  reduce n (add x (c, (map Var_o xs)) env) (snd arm)
                | Lambda.Var_p y => 
                  (* in this branch, substitute x for y *)
                  reduce n env (CopyProp.cprop (add y (Var_o x) empty) (snd arm))
              end)
          in
          let find_arm :=
            fix find (c:constructor)(arms:list (pattern*exp)) : option (pattern*exp) :=
            match arms with
              | nil => None
              | (Lambda.Con_p c' xs,e)::rest =>
                if eq_dec c c' then Some (Lambda.Con_p c' xs,e) else find c rest
              | (Lambda.Var_p x,e)::rest => Some (Lambda.Var_p x,e)
            end 
          in
          match e with
            | Match_e (Var_o x) arms =>
              match find x env with
                | Some (c,vs) =>
                  (* earlier, we had Let_e x c vs, so we can reduce the match *)
                  match find_arm c arms with
                    | Some (Lambda.Con_p _ ys,ec) =>
                      reduce n env (CopyProp.cprop (add_all empty ys vs) ec)
                    | Some (Lambda.Var_p y,ec) =>
                      reduce n env (CopyProp.cprop (add y (Var_o x) empty) ec)
                    | _ => e
                  end
                | None =>
                  (* we can't reduce this match, but we can reduce nested matches
                     on the same variable. *)
                  Match_e (Var_o x) (List.map (reduce_arm x) arms)
              end
            | Match_e (Con_o c) arms =>
             (* this is a special case for the nullary constructors *)
              match find_arm c arms with
                | Some (Lambda.Con_p _ _,ec) => reduce n env ec
                | _ => e
              end
            | Let_e x c vs e =>
              Let_e x c vs (reduce n (add x (c,vs) env) e)
            | Letrec_e fs e =>
              Letrec_e
              (List.map (fun fn =>
                match fn with
                  | (f,(xs,e)) => (f,(xs,reduce n env e))
                end) fs) (reduce n env e)
            | App_e v vs => App_e v vs
          end
      end.
  End with_env.

End MatchRed.

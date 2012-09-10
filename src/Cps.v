Require Import Lambda.
Require Import String List.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad ExtLib.Monad.ContMonad.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Module CPS.
  Definition var := Lambda.var.
  Definition constructor := Lambda.constructor.
  Definition pattern := Lambda.pattern.
  Definition env_t := Lambda.env_t.

  Inductive op : Type := 
  | Var_o : var -> op
  | Con_o : constructor -> op.

  Inductive exp : Type := 
  | App_e : op -> list op -> exp
  | Let_e : var -> constructor -> list op -> exp -> exp
  | Match_e : op -> list (pattern * exp) -> exp
  | Letrec_e : env_t (list var * exp) -> exp -> exp.

  Definition K (Ans : Type) := contT Ans (state nat).

  Hint Transparent K : typeclass_instances.

  Local Open Scope string_scope.
  Import MonadNotation.

  (** Get a fresh temporary variable **)
  Definition freshTemp {Ans} (x:string) : K Ans var :=
    n <- lift (Lambda.fresh x) ;
    ret ("$" ++ n).

  (** apply [f] before returning the result of [k] **)
  Definition plug (f : exp -> exp) (x : op) : K exp op :=
    mapContT (liftM f) (ret x).
  (* fun k n => let (n',e) := k x n in (n', f e). *)

  Notation "f [[ x ]]" := (plug f x) 
    (at level 84).

  Definition LetLam_e (f:var) (xs: list var) (e:exp) (e':exp) : exp := 
    Letrec_e ((f,(xs,e))::nil) e'.

  Definition match_eta (x:var) (e:exp) := 
    match e with 
      | App_e op1 ((Var_o y)::nil) => 
        if rel_dec y x then Some op1 else None
      | _ => None
    end.

  Definition App_k (v1 v2:op) : K exp op :=
    a <- freshTemp "a" ; 
    f <- freshTemp "f" ; 
    mapContT (fun c =>
      e <- c ;
      ret match match_eta a e with
            | None => LetLam_e f (a::nil) e (App_e v1 (v2::(Var_o f)::nil))
            | Some op => App_e v1 (v2::op::nil)
          end) (ret (Var_o a)).

  (** run to an exp, the [e] making it call the continuation [c] when done **)
  Definition run (e:K exp op) (c : var) : state nat exp :=
    runContT e (fun v => ret (App_e (Var_o c) (v::nil))).

  Section mapM.
    Context {A B : Type}.
    Context {m : Type -> Type}.
    Context {M : Monad m}.
    Variable f : A -> m B.

    Fixpoint mapM (ls : list A) : m (list B) :=
      match ls with
        | nil => ret nil
        | l :: ls => 
          l <- f l ;
          ls <- mapM ls ;
          ret (l :: ls)
      end.
  End mapM.

  Fixpoint cps (e:Lambda.exp) : K exp op :=
    match e with 
      | Lambda.Var_e x => ret (Var_o x)
      | Lambda.Con_e c nil => ret (Con_o c)
      | Lambda.Con_e c es => 
        ops <- (fix cps_list (es:list Lambda.exp) (ops:list op) : K exp (list op) := 
                match es with 
                  | nil => ret (List.rev ops)
                  | e::es' => op <- cps e ; cps_list es' (op::ops)
                end) es nil ; 
        x <- freshTemp "x" ; 
        (Let_e x c ops [[ Var_o x ]])
      | Lambda.Let_e x e1 e2 => 
        v1 <- cps e1 ;
        mapContT (fun c2 => 
          e2' <- c2 ;
          ret (Match_e v1 ((Lambda.Var_p x, e2')::nil))) (cps e2)
        (*
           (fun k n => 
          let (n', e2') := cps e2 k n in
            (n', Match_e v1 ((Lambda.Var_p x, e2')::nil)))
        *)
      | Lambda.App_e e1 e2 => 
        v1 <- cps e1 ; v2 <- cps e2 ; App_k v1 v2
      | Lambda.Lam_e x e => 
        f <- freshTemp "f" ; 
        c <- freshTemp "c" ;
        e' <- lift (run (cps e) c) ;
        (LetLam_e f (x::c::nil) e' [[ Var_o f ]])
      | Lambda.Letrec_e fs e => 
        fs' <- (fix cps_fns (fs:env_t (var*Lambda.exp)) (cpsfs:env_t (list var * exp)) : K exp (env_t (list var * exp)) := 
                match fs with 
                  | nil => ret (List.rev cpsfs)
                  | (f,(x,e))::fs' => 
                    c <- freshTemp "c" ;
                    e' <- lift (run (cps e) c) ;
                    cps_fns fs' ((f,(x::c::nil, e'))::cpsfs)
                end) fs nil ; 
        v <- cps e ; 
        (Letrec_e fs' [[ v ]])
      | Lambda.Match_e e arms =>  
        v <- cps e ; 
        c <- freshTemp "c" ; 
        x <- freshTemp "x" ;
        arms' <- lift (mapM (fun p_e => e' <- run (cps (snd p_e)) c ; ret (fst p_e, e')) arms) ;
        mapContT (fun cc : state nat exp => z <- cc ; ret (LetLam_e c (x :: nil) z (Match_e v arms'))) (ret (Var_o x))
(*
        (fun k n => 
          let (n, cont) := k (Var_o x) n in 
            (fix cps_arms (arms:list (pattern * Lambda.exp)) (cpsarms:list (pattern * exp)) : nat -> (nat * exp) := 
                  match arms with 
                    | nil => 
                      fun n => 
                        (n, LetLam_e c (x::nil) cont (Match_e v (List.rev cpsarms)))
                    | (p,e)::arms' => 
                      fun n => 
                        let (n', e') := cps e (fun v n => (n, App_e (Var_o c) (v::nil))) n in 
                          cps_arms arms' ((p,e')::cpsarms) n'
                  end) arms nil n)
*)
    end.
  
  Definition CPS (e:Lambda.exp) : exp := 
    evalState (runContT (cps e) (fun v => ret (App_e (Var_o "halt") (v::nil)))) 0.

End CPS.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.

Set Implicit Arguments.
Set Strict Implicit.

Section DEADCODE.
  Import CPSK.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition Count := alist (var + cont) nat.

  Definition Monoid_Count : Monoid Count :=
  {| monoid_unit := Maps.empty
   ; monoid_plus := fun x y => Maps.combine (fun k x y => x + y) x y
  |} .

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {State_m : MonadWriter Monoid_Count m}.

  Definition useV (v : var) : m unit :=
    tell (Maps.singleton (inl v) 1).
  (* modify (Monoid_Count.(monoid_plus) (Maps.singleton (inl v) 1)) ;; ret tt. *)

  Definition useC (v : cont) : m unit :=
    tell (Maps.singleton (inr v) 1).
(*
    modify (Monoid_Count.(monoid_plus) (Maps.singleton (inr v) 1)) ;; ret tt. *)

  Definition useOp (o : op) : m unit :=
    match o with
      | Var_o v => useV v
      | _ => ret tt
    end.

  Definition checkUse {T U} (c : m T) (test : Count -> bool) (no : T -> m U) (yes : T -> m U) : m U.
  refine (
    x <- listen c ;;
    if test (snd x) then 
      yes (fst x)
    else
      no (fst x)
  ).
  Defined.

  Definition ignore {T} (ls : list (var + cont)) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove x mp) ls).

  Definition ignoreKs {T} (ls : list var) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove (inl x) mp) ls).

  Definition ignoreVs {T} (ls : list cont) : m T -> m T :=
    censor (List.fold_left (fun mp x => Maps.remove (inr x) mp) ls).

  Definition used (v : var + cont) (c : Count) : bool :=
    match Maps.lookup v c with
      | None => false
      | Some 0 => false
      | _ => true
    end.

(*
  Definition used (v : var) : m bool :=
    c <- gets (Maps.lookup (inl v)) ;;
    match c with
      | None => ret true
      | Some c =>
        ret (eq_dec c 0)
    end.
*)

  Fixpoint dce (e : exp) : m exp.
  refine(
    match e with
      | App_e x ks xs =>
        useOp x ;; iterM useOp xs ;; iterM useC ks ;;
        ret (App_e x ks xs)
      | Let_e d e =>
        checkUse (dce e) 
          (fun cts => 
            match d with
              | Fn_d x _ _ _ => used (inl x) cts
              | Op_d x _ => used (inl x) cts
              | Bind_d x w _ _ => used (inl x) cts || used (inl w) cts
              | Prim_d x _ _ => used (inl x) cts
            end)
          (fun e => ret e)
          (fun e => 
            d <- match d with 
                   | Fn_d x ks xs e =>
                     e <- ignoreKs ks (ignoreVs xs (dce e)) ;;
                     ret (Fn_d x ks xs e)
                   | Op_d x o =>
                     useOp o ;; ret (Op_d x o)
                   | Prim_d x p os => 
                 u <- used x ;;
                 if u then
                   iterM useOp os ;; ret (Some (Prim_d x p os))
                 else
                   ret None
               | Bind_d x w m os =>
                 u1 <- used x ;; u2 <- used w ;;
                 if u1 || u2 then
                   iterM useOp os ;; ret (Some (Bind_d x w m os))
                 else
                   ret None
             end ;;
        match d with
          | None => ret e
          | Some d => ret (Let_e d e)
        end        
      | _ => _
    end).
    

  (** Calculate the number of uses of a variable (i.e., free occurrences) and
      return an environment mapping variables to counts.  *)
  Definition counts := alist var nat.

  Definition clear_count (x:var) : ST counts unit :=
    s <- get ;; put (update x 0 s).

  Definition inc_count (x:var) : ST counts unit :=
    s <- get ;;
    match lookup x s with
      | None => put (update x 1 s)
      | Some c => put (update x (1+c) s)
    end.

  Definition use_op (v:op) : ST counts unit :=
    match v with
      | Var_o x => inc_count x
      | Con_o _ => ret tt
    end.

  Definition use_pat (p:pattern) : ST counts unit :=
    match p with
      | Lambda.Con_p _ xs => iter clear_count xs
      | Lambda.Var_p x => clear_count x
    end.

  Fixpoint uses (e:exp) : ST counts unit :=
    match e with
      | App_e v vs => use_op v ;; iter use_op vs
      | Let_e x c vs e =>
        iter use_op vs ;; clear_count x ;; uses e
      | Match_e v arms =>
        use_op v ;;
        iter (fun (arm:pattern*exp) => use_pat (fst arm) ;; uses (snd arm)) arms
      | Letrec_e fs e =>
        iter (fun fn => match fn with
                          | (f,(xs,e)) => clear_count f ;; iter clear_count xs
                        end) fs ;;
        iter (fun fn => match fn with | (_,(_,e)) => uses e end) fs ;;
        uses e
    end.

  Definition calc_uses (e:exp) : counts := snd (runState (uses e) nil).


    (** Assume we have usage counts for each variable -- this gets lambda
        abstracted outside the section for each function that uses this. *)
    Variable cs : counts.

    (** Determine whether a let-bound or letrec-bound variable is "dead"
       (has a use-count of zero) and if so, eliminate it.  Note that this
       will never get rid of a truly recursive function. *)
    Definition is_dead (fn : (var * (list var * exp))) :=
      match lookup (fst fn) cs with
        | Some 0 => true
        | _ => false
      end.

    (** Eliminate dead bindings -- i.e., that have a use-count of zero. *)
    Fixpoint dead(e:exp) : exp :=
      match e with
        | App_e _ _ => e
        | Let_e x c vs e' =>
          match lookup x cs with
            | Some 0 => dead e'
            | _ => Let_e x c vs (dead e')
          end
        | Match_e v arms =>
          Match_e v (List.map (fun arm => (fst arm, dead (snd arm))) arms)
        | Letrec_e fs e =>
          let fs' := List.map (fun fn => (fst fn, (fst (snd fn), dead (snd (snd fn))))) fs in
          let gs := filter (fun x => negb (is_dead x)) fs' in
            match gs with
              | nil => dead e
              | _ => Letrec_e gs (dead e)
            end
      end.

    (** Count the number of times a function is called *)
    Fixpoint calls (e:exp) : ST counts unit := 
      match e with 
        | App_e (Var_o x) _ => use_op (Var_o x)
        | App_e _ _ => ret tt
        | Let_e x c vs e => calls e
        | Match_e v arms => 
          iter (fun (arm:pattern*exp) => calls (snd arm)) arms
        | Letrec_e fs e => 
          iter (fun fn => clear_count (fst fn)) fs ;; 
          iter (fun fn => calls (snd (snd fn))) fs ;;
          calls e
      end.

    (** Assume we have calculated the numer of calls for each function in an environment. *)
    Variable num_calls : env_t nat.

    (** Claim:  A letrec function f can be safely inlined if it is called in exactly
        one spot, and there are no other uses of the function.  (Is this correct?
        Consider the case of a letrec with two functions f and g that call each
        other and there are no other calls.  Then there's no way to enter the loop!
        So f and g must be dead code.  If one of the functions (say f) has another call 
        site, then we can still safely inline g into f. *)
    Definition called_once (fn:var * (list var * exp)) : bool := 
      let (f,_) := fn in 
      match lookup f num_calls, lookup f cs with 
        | Some 1, Some 1 => true
        | _, _ => false
      end.

    (* Again, fusing the copy propagation with the inline1 pass would make
       this more efficient.  Note that inlining a function that is called
       at most once preserves the property that each variable is uniquely
       named.  So generalizing this to multiple uses requires a bit more
       work, as we must pick fresh variable names for each copy of a function
       that we inline. 
       *)
    Fixpoint inline1 (defs:env_t (list var * exp)) (e:exp) : exp :=
        match e with
          | App_e (Var_o f) vs =>
            match lookup f defs with
              | None => e
              | Some (xs,e') => cprop (substs xs vs) e'
            end
          | App_e _ _ => e
          | Let_e x c vs e => Let_e x c vs (inline1 defs e)
          | Match_e v arms =>
            Match_e v (map (fun arm => (fst arm, inline1 defs (snd arm))) arms)
          | Letrec_e fs e =>
            let defs' := (filter called_once fs) ++ defs in 
              let fs' := 
                filter (fun fn => negb (called_once fn)) 
                (map (fun fn => (fst fn, (fst (snd fn), inline1 defs' (snd (snd fn))))) fs) in
                match fs' with
                  | nil => (inline1 defs' e)
                  | fs' => Letrec_e fs' (inline1 defs' e)
                end
        end.

  End DEADCODE.
Require Import Lambda Cps.
Require Import ZArith String List Bool.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad ExtLib.Monad.ContMonad.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

(** In this module, we define a few simple reduction optimizations.
    We will ultimately want to break these out into separate modules,
    provide a number of regression tests, use better data structures,
    and fuse the passes as best we can.
*)

(** To do for the current code:
    - use a better finite map data structure for environments
    - fuse reduction with other transformations to make them linear time
    - fuse some of the optimizations together a la Jim & Appel?
    - split out non-recursive functions from recursive functions
    - add distinction between continuations & user-level functions (and calls)?

   To do for future basic optimizations:
    - common sub-expression elimination (CSE)
      - the interesting part of this is function calls in the CPS setting
    - splitting mutually recursive functions that aren't really recursive
      (strongly connected components), supporting better dead-code and
      inline-once optimization.
    - general inlining for functions
    - partial redundancy elimination

   To do for loop optimizations:
    - loop invariant removal, including loop invariant arguments
    - interprocedural copy propagation, reduction, and CSE

   To do for general engineering:
    - break optimizations into separate files
    - better test/regression infrastructure
*)
Module Optimize.
  Import MonadNotation CPS.
  Local Open Scope monad_scope.
  (** The optimizer (and much of the compiler) is going to want to use
      some sort of environment:  a finite map from variables to some type
      of information.  Here, I've just used association lists, but obviously,
      we need to rip this out, put it in a different module, and use
      something with good asymptotic behavior (i.e., a balanced tree.)

      Ultimately, we may want to use numbers to represent variables so
      that we can get efficient indexing...
  *)

  Definition initial_env {A} : env_t A := nil.

  Fixpoint update {A} (x:var) (c:A) (xs:env_t A) : env_t A :=
    match xs with
      | nil => (x,c)::nil
      | (y,k)::t => if eq_dec y x then (y,c)::t else (y,k)::(update x c t)
    end.

  Fixpoint lookup {A} (x:var) (xs:env_t A) : option A :=
    match xs with
      | nil => None
      | (y,c)::t => if eq_dec y x then Some c else lookup x t
    end.

  Definition extend {A} (xs:env_t A) (x:var) (v:A) : env_t A :=
    (x,v)::xs.

  Fixpoint substs {A} (xs:list var) (vs:list A) : env_t A :=
    match xs, vs with
      | x::xs, v::vs => extend (substs xs vs) x v
      | _, _ => initial_env
    end.

  (** * Reduction:  includes simple copy and constant propagation, plus constant folding,
     simple switch reduction, and a few other things (e.g., eta reduction). *)
  Definition reduce_op(subst: env_t decl)(v:op) : op :=
    match v with
      | Var_o x => match lookup x subst with
                     | Some (Op_d _ v') => v'
                     | _ => v
                   end
      | _ => v
    end.

  Fixpoint find_arm (v:op) (arms : list (pattern * exp)) (def: option exp) :=
    match v, arms, def with
      | Var_o _, _, _ => None
      | v, nil, None => None
      | v, nil, Some e => Some e
      | Con_o c, ((Int_p _,_)::_), _ => None
      | Int_o i, ((Con_p _,_)::_), _ => None
      | Con_o c, ((Con_p c',e)::arms), def => if eq_dec c c' then Some e else find_arm v arms def
      | Int_o i, ((Int_p i',e)::arms), def => if eq_dec i i' then Some e else find_arm v arms def
    end.

  Definition same_op(v1 v2:op) : bool :=
    match v1, v2 with
      | Int_o i, Int_o j => eq_dec i j
      | Con_o c, Con_o c' => eq_dec c c'
      | Var_o x, Var_o y => eq_dec x y
      | _, _ => false
    end.

  Definition diff_op(v1 v2:op) : bool :=
    match v1, v2 with
      | Int_o i, Int_o j => negb (eq_dec i j)
      | Con_o c, Con_o c' => negb (eq_dec c c')
      | _, _ => false
    end.

  Definition reduce_primop(subst:env_t decl)(p:primop) (vs:list op) : option op :=
    match p, vs with
      | Plus_p, (v::(Int_o 0)::nil) => Some v
      | Plus_p, ((Int_o 0)::v::nil) => Some v
      | Plus_p, ((Int_o i)::(Int_o j)::nil) => Some (Int_o (i+j))
      | Minus_p, (v::(Int_o 0)::nil) => Some v
      | Minus_p, ((Int_o i)::(Int_o j)::nil) => Some (Int_o (i-j))
      | Times_p, ((Int_o 1)::v::nil) => Some v
      | Times_p, (v::(Int_o 1)::nil) => Some v
      | Times_p, ((Int_o i)::(Int_o j)::nil) => Some (Int_o (i*j))
      | Eq_p, (v1::v2::nil) => if same_op v1 v2 then Some (Con_o "true"%string) else None
      | Neq_p, (v1::v2::nil) => if diff_op v1 v2 then Some (Con_o "true"%string) else None
      | Lt_p, ((Int_o i)::(Int_o j)::nil) =>
        Some (Con_o (if Z.ltb i j then "true" else "false")%string)
      | Lte_p, ((Int_o i)::(Int_o j)::nil) =>
        Some (Con_o ((if orb (Z.ltb i j) (Z.eqb i j) then "true" else "false")%string))
      | Ptr_p, ((Con_o _)::nil) => Some (Con_o "false"%string)
      | Ptr_p, ((Var_o x)::nil) =>
        match lookup x subst with
          | Some (Prim_d _ MkTuple_p vs) => Some (Con_o "true"%string)
          | _ => None
        end
      | Proj_p, ((Int_o i)::(Var_o x)::nil) =>
        match lookup x subst with
          | Some (Prim_d _ MkTuple_p vs) => nth_error vs (Z.abs_nat i)
          | _ => None
        end
      | _, _ => None
    end.

  Definition pat2op(p:pattern) : op :=
    match p with
      | Con_p c => Con_o c
      | Int_p i => Int_o i
    end.

  Fixpoint reduce_exp(subst: env_t decl)(e:exp) : exp :=
    match e with
      | App_e v vs => App_e (reduce_op subst v) (map (reduce_op subst) vs)
      | Let_e d e =>
        match reduce_decl subst d with
          | (None, subst') => reduce_exp subst' e
          | (Some d',subst') => Let_e d' (reduce_exp subst' e)
        end
      | Switch_e v arms def =>
        let v' := reduce_op subst v in
        let arms' :=
          map (fun p => (fst p,
            match v' with
              | Var_o x => reduce_exp (extend subst x (Op_d x (pat2op (fst p)))) (snd p)
              | _ => reduce_exp subst (snd p)
            end)) arms in
        let def' := option_map (reduce_exp subst) def in
          match find_arm v' arms' def' with
            | None => SimplSwitch_e v' arms' def'
            | Some e => e
          end
      | Halt_e o => Halt_e (reduce_op subst o)
    end
  with reduce_decl (subst:env_t decl) (d:decl) : option decl * env_t decl :=
    match d with
      | Op_d x v => (None, extend subst x (Op_d x (reduce_op subst v)))
      | Prim_d x p vs =>
        let vs' := map (reduce_op subst) vs in
        match reduce_primop subst p vs' with
          | None => let d := Prim_d x p vs' in (Some d, extend subst x d)
          | Some v => (None, extend subst x (Op_d x v))
        end
      | Fn_d f xs e =>
        let e' := reduce_exp subst e in
          match match_etas xs e with
            | None => (Some (Fn_d f xs (reduce_exp subst e)), subst)
            | Some v => (None, extend subst f (Op_d f v))
          end
      | Rec_d ds =>
        match List.fold_right (fun d p =>
                                 match reduce_decl (fst p) d with
                                   | (None, subst) => (subst, snd p)
                                   | (Some d, subst) => (subst, d::(snd p))
                                 end) (subst, nil) ds with
          | (subst, nil) => (None, subst)
          | (subst, ds) => (Some (Rec_d ds), subst)
        end
    end.

  Definition reduce (e:exp) : exp := reduce_exp initial_env e.

  Section COUNTS.
    (** * Counting the number of uses of a variable -- assumes that each
          variable is uniquely named. *)
    Definition counts := env_t nat.
    Definition clear_count (x:var) : state counts unit :=
      s <- get ; put (update x 0 s).

    Definition inc_count (x:var) : state counts unit :=
      s <- get ;
      match lookup x s with
        | None => put (update x 1 s)
        | Some c => put (update x (1+c) s)
      end.

    Definition use_op (v:op) : state counts unit :=
      match v with
        | Var_o x => inc_count x
        | Con_o _ => ret tt
        | Int_o _ => ret tt
      end.

    Fixpoint uses_exp (e:exp) : state counts unit :=
      match e with
        | App_e v vs => use_op v ;; iter use_op vs
        | Let_e d e => uses_decl d ;; uses_exp e
        | Switch_e v arms def =>
          use_op v ;; iter (fun p => uses_exp (snd p)) arms ;;
          match def with None => ret tt | Some e => uses_exp e end
        | Halt_e o => use_op o
      end
    with uses_decl (d:decl) : state counts unit :=
      match d with
        | Op_d x v => use_op v
        | Prim_d x p vs => iter use_op vs ;; clear_count x
        | Fn_d f xs e => uses_exp e
        | Rec_d ds => iter uses_decl ds
      end.

    Definition calc_uses (e:exp) : counts := snd (runState (uses_exp e) initial_env).

    Variable use_counts : counts.

    (** * Simple dead code elimination -- eliminates a decl that is used zero times. *)
    Fixpoint dead_exp (e:exp) : exp :=
      match e with
        | App_e _ _ => e
        | Let_e d e => match dead_decl d with
                         | None => dead_exp e
                         | Some d' => Let_e d' (dead_exp e)
                       end
        | Switch_e v arms def =>
          Switch_e v (map (fun p => (fst p, dead_exp (snd p))) arms) (option_map dead_exp def)
        | Halt_e o => e
      end
    with dead_decl (d:decl) : option decl :=
      match d with
        | Prim_d x _ _ => match lookup x use_counts with | Some 0 => None | _ => Some d end
        | Op_d x _ => match lookup x use_counts with | Some 0 => None | _ => Some d end
        | Fn_d f xs e =>
          match lookup f use_counts with
            | Some 0 => None
            | _ => Some (Fn_d f xs (dead_exp e))
          end
        | Rec_d ds =>
          match fold_right (fun d ds' => match dead_decl d with
                                           | Some d => d :: ds'
                                           | None => ds'
                                         end) nil ds with
            | nil => None
            | ds' => Some (Rec_d ds')
          end
      end.

    (** * Calculate the number of times a function is called in preparation for
          inlining. *)
    Fixpoint calls_exp (e:exp) : state counts unit :=
      match e with
        | App_e v vs => use_op v
        | Let_e d e => calls_decl d ;; calls_exp e
        | Switch_e _ arms def =>
          iter (fun p => calls_exp (snd p)) arms ;;
          match def with None => ret tt | Some e => calls_exp e end
        | Halt_e o => ret tt
      end
    with calls_decl (d:decl) : state counts unit :=
      match d with
        | Op_d _ _ => ret tt
        | Prim_d _ _ _ => ret tt
        | Fn_d f xs e => calls_exp e
        | Rec_d ds => iter calls_decl ds
      end.

    Definition calc_calls (e:exp) : counts := snd (runState (calls_exp e) initial_env).

    Variable call_counts : counts.

    Fixpoint bind_args (xs:list var) (vs:list op) (e:exp) : exp :=
      match xs, vs with
        | x::xs, v::vs => Let_e (Op_d x v) (bind_args xs vs e)
        | _, _ => e
      end.

    (** Returns true when [f] is called exactly once and there are no other uses for [f]. *)
    Definition called_once (f:var) : bool :=
      match lookup f call_counts, lookup f use_counts with
        | Some 1, Some 1 => true
        | _, _ => false
      end.

    (** Inline functions called only once and that otherwise aren't used. *)
    Fixpoint inline1_exp (env : env_t (list var * exp)) (e:exp) : exp :=
      match e with
        | App_e (Var_o x) vs =>
          match lookup x env with
            | None => e
            | Some (xs,e) => bind_args xs vs e
          end
        | App_e _ _ => e
        | Let_e d e =>
          match inline1_decl false env d with
            | (None, env') => inline1_exp env' e
            | (Some d', env') => Let_e d' (inline1_exp env' e)
          end
        | Switch_e v arms def =>
          Switch_e v (map (fun p => (fst p, inline1_exp env (snd p))) arms)
            (option_map (inline1_exp env) def)
        | Halt_e o => e
      end
    (** We keep track of whether the declaration is in a [Rec_d] and if so, we don't
        add the declaration to those to be inlined to avoid some problems (see below). *)
    with inline1_decl (in_rec:bool) (env : env_t (list var * exp)) (d:decl) : (option decl) * (env_t (list var * exp)) :=
      match d with
        | Op_d _ _ => (Some d, env)
        | Prim_d _ _ _ => (Some d, env)
        | Fn_d f xs e =>
          let e' := inline1_exp env e in
            if called_once f && negb in_rec then (None, extend env f (xs,e')) else (Some (Fn_d f xs e'),env)
        | Rec_d ds =>
          (** We really ought to add to the environment the definitions of all functions
              to be inlined, before processing the bodies of the functions. But the problem
              is that before entering them into the environment, we should go ahead and
              inline any calls within them.  Since it's hard to figure out the "right" order
              to do things in, I simply never inline recursive functions using this routine.
              We can make up for this by (a) writing something to break out functions that
              aren't really recursive, and (b) treating this properly in the general
              inlining mechanism. *)
          match fold_right (fun d (p:list decl * env_t (list var * exp)) =>
                             let (ds,env) := p in
                               match inline1_decl true env d with
                                 | (None,env') => (ds,env')
                                 | (Some d,env') => (d::ds,env')
                               end) (nil,env) ds with
            | (nil,env) => (None,env)
            | (ds,env) => (Some(Rec_d ds),env)
          end
      end.

  End COUNTS.

  Definition deadcode (e:exp) : exp :=
    let uses := calc_uses e in
      dead_exp uses e.

  Definition inline_once (e:exp) : exp :=
    let uses := calc_uses e in
      let calls := calc_calls e in inline1_exp uses calls initial_env e.

  (** Our optimizer iterates [n] times. Really, we ought to check to see if any
      change occurred and stop early if no change has occured. *)
  Fixpoint optimize (n:nat) (e:exp) : exp :=
    match n with
      | 0 => e
      | S n => optimize n (reduce (deadcode (inline_once e)))
    end.

  (*
  Section TEST_OPTIMIZER.
     Import LambdaNotation.
     Eval compute in (exp2string (CPS test_exp)).
     Eval compute in (exp2string (optimize 2 (CPS test_exp))).
     Eval compute in (exp2string (CPS (gen e1))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e1)))).
     Eval compute in (exp2string (CPS (gen e2))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e2)))).
     Eval compute in (exp2string (CPS (gen e3))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e3)))).
     Eval compute in (exp2string (CPS (gen e4))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e4)))).
     Eval compute in (exp2string (CPS (gen e5))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e5)))).
     Eval compute in (exp2string (CPS (gen e6))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e6)))).
     Eval compute in (exp2string (CPS (gen e7))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e7)))).
     Eval compute in (exp2string (CPS (gen e8))).
     Eval compute in (exp2string (optimize 2 (CPS (gen e8)))).
  End TEST_OPTIMIZER.
  *)

End Optimize.

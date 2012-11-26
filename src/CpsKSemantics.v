Require Import List String.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsK CoqCompile.Env.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Programming.Show.
Require Import ZArith.


Set Implicit Arguments.
Set Strict Implicit.

Section CPSEVAL.
  Import CPSK.
  Import MonadNotation.
  Local Open Scope string_scope.
  Local Open Scope monad_scope.
  (** Because this version of CPS supports recursive records, as well as recursive
      functions, I've chosen to use an allocation-style semantics here, where large
      values, such as tuples and closures, are allocated on a heap.  Then, to build
      circular values, such as recursive closures or recursive tuples, we first 
      allocate space for them, then initialize them with back-patching. *)

  (** Small values *)
  Inductive value : Type := 
  | Con_v : Lambda.constructor -> value
  | Int_v : Z -> value
  | Ptr_v : nat -> value
  | World_v : value.
  
  (** Allocated values *)
  Inductive heap_value : Type := 
  | Tuple_v : list value -> heap_value
  | Closure_v : alist var value -> list var -> exp -> heap_value.
  
  (** We'll just naively implement heaps as lists of heap values *)
  Definition heap := list heap_value.

  Definition m : Type -> Type := stateT heap (stateT (list (mop * list value)) (sum string)).
  
  (** We'll be working in a combination of the state and option monads, so
     I've written various environment and other functions tailored to that
     monad. *)
  Fixpoint lookup {A} (env:alist var A) (x:var) : m A := 
    match env with 
      | nil => raise ("unknown variable " ++ to_string x)
      | (y,v)::rest => if eq_dec y x then ret v else lookup rest x 
    end.

  Definition extend {A} (env:alist var A) (x:var) (v:A) : alist var A := (x,v)::env.

  Fixpoint extends {A}(env:alist var A) (xs:list var) (vs:list A) : m (alist var A) := 
    match xs, vs with 
      | nil, nil => ret env
      | x::xs, v::vs => extends (extend env x v) xs vs
      | _, _ => raise "calling function with wrong # of arguments"
    end.

  Definition eval_op (env:alist var value) (v:op) : m value := 
    match v with 
      | Con_o c => ret (Con_v c)
      | Int_o i => ret (Int_v i)
      | Var_o x => lookup env x
      | InitWorld_o => ret World_v
    end.

  (** Find the appropriate switch arm for a given small value. *)
  Fixpoint find_arm (v:value) (arms : list (pattern * exp)) (def:option exp) : m exp := 
    match v,arms with 
      | _,nil => match def with
                   | None => raise "bad pattern match"
                   | Some e => ret e 
                 end
      | Con_v c, ((Con_p c',e)::rest) => if eq_dec c c' then ret e else find_arm v rest def
      | Int_v i, ((Int_p i',e)::rest) => if eq_dec i i' then ret e else find_arm v rest def
      | _,(_::rest) => find_arm v rest def
    end.

  (** Allocate a heap value and return its address as a pointer *)
  Definition malloc(v:heap_value) : m value :=
    h <- get ;;
    let _ : heap := h in
    put (List.app h (v::nil)) ;; 
    ret (Ptr_v (List.length h)).

    (** Lookup the pointer [n] in the heap. *)
  Definition heap_lookup (n:nat) : m heap_value := 
    h <- get ; 
    match nth_error h n with 
      | None => raise "bad heap pointer"
      | Some v => ret v
    end.

  Fixpoint heap_upd (n:nat) (h:heap) (v:heap_value) : option heap := 
    match n, h with 
      | 0, _::tail => ret (v::tail)
      | S n, head::tail => t <- (heap_upd n tail v) ; ret (head::t)
      | _, _ => None
    end.

  (** Update the heap value at location [n] to be the value [v]. *)
  Definition heap_set (n:nat) (v:heap_value) : m unit := 
    h <- get ; 
    match heap_upd n h v with 
      | None => raise "bad heap pointer" 
      | Some h' => put h'
    end.

  (** Evaluate the primops given closed values *)      
  Definition eval_primop (p:primop) (vs: list value) : m value := 
    match p, vs with 
      | Eq_p, (Int_v i)::(Int_v j)::nil => ret (if eq_dec i j then (Con_v "true") else (Con_v "false"))
      | Eq_p, (Con_v i)::(Con_v j)::nil => ret (if eq_dec i j then (Con_v "true") else (Con_v "false"))
      | Neq_p, (Int_v i)::(Int_v j)::nil => ret (if eq_dec i j then (Con_v "false") else (Con_v "true"))
      | Neq_p, (Con_v i)::(Con_v j)::nil => ret (if eq_dec i j then (Con_v "false") else (Con_v "true"))
      | Lt_p, (Int_v i)::(Int_v j)::nil => ret (if Z.ltb i j then (Con_v "true") else (Con_v "false"))
      | Lte_p, (Int_v i)::(Int_v j)::nil => ret (if orb (Z.ltb i j) (eq_dec i j) 
        then (Con_v "true") else (Con_v "false"))
      | Ptr_p, ((Int_v _)::nil) => ret (Con_v "false")
      | Ptr_p, ((Con_v _)::nil) => ret (Con_v "false")
      | Ptr_p, ((Ptr_v _)::nil) => ret (Con_v "true")
      | Plus_p, ((Int_v i)::(Int_v j)::nil) => ret (Int_v (i+j))
      | Minus_p, ((Int_v i)::(Int_v j)::nil) => ret (Int_v (i-j))
      | Times_p, ((Int_v i)::(Int_v j)::nil) => ret (Int_v (i*j))
          (** Note allocation here *)
      | MkTuple_p, vs => malloc (Tuple_v vs)
      | Proj_p, ((Int_v i)::(Ptr_v n)::nil) => 
          (** Lookup the pointer in the heap to get a heap value [v] *)
        v <- heap_lookup n ; 
        match v with 
            (** Check that [v] is a tuple *)
          | Tuple_v vs => 
            match nth_error vs (Z.abs_nat i) with 
              | None => raise "projection out of bounds"
              | Some v => ret v
            end
          | _ => raise "projection from non-tuple"
        end
      | _, _ => raise "bad primitive application" 
    end.

    (** Used for initializing variables to some pointer value to a dummy
       heap value in a circular set of definitions. *)
  Definition malloc_dummy (d:decl) : m (var * value) := 
    match d with 
      | Fn_d f ks _ _ => v <- malloc (Tuple_v nil) ;; ret (f,v)
      | Prim_d x MkTuple_p _ => 
        v <- malloc (Tuple_v nil) ;; 
        ret (x,v)
      | _ => raise "can not allocate non function or tuple"
    end.

    (** Assuming we've already bound the declared variable in [d] to a pointer
        value [p], we now actually build the appropriate value under this 
        extended environment.  Then we set [p] to point to the new value.
        So for instance, if we have:

        let rec x = MkTuple [x;x]

        then we first allocate a dummy empty tuple at location [p] and update
        the environment so [x] maps to [p].  Then we actually build the 
        tuple, evaluating the components to closed values.  In this case,
        we'd get a [Tuple_v [p;p]].  Finally, we set [p] to point to this
        heap value.  So in the end, we have an environment that maps [x] to
        [p], and a heap that maps [p] to [Tuple_v [p;p]].  

        Note that we only support recursion on functions and tuples and not,
        in general, on arbitrary declarations.  This ensures that we don't
        end up evaluating something that eliminates a pointer (e.g., projection,
        or function call) when we haven't completed initializing the expression.

        Another advantage of making this all explicit is that it's quite
        close to what we'll do at the machine level.
     *)
  Definition initialize_decl (env:alist var value) (d: decl) : m unit :=
    match d with 
      | Fn_d f ks xs e => 
        v <- lookup env f ;;
        match v with 
          | Ptr_v n => heap_set n (Closure_v env xs e)
          | _ => raise "??"
        end
      | Prim_d x MkTuple_p vs => 
        vs' <- mapM (eval_op env) vs ;;
        v <- lookup env x ; 
        match v with 
          | Ptr_v n => heap_set n (Tuple_v vs')
          | _ => raise "??"
        end
      | _ => raise "??"
    end.

  Definition sideEffect (mo : mop) (ls : list value) : m unit :=
    modify (T := list (mop * list value)) (fun x => List.app x ((mo, ls) :: nil)) ;;
    ret tt.

  Fixpoint eval_decl (env:alist var value) (d:decl) : m (alist var value) := 
    match d with 
      | Op_d x v =>
        v' <- eval_op env v ;;
        ret (extend env x v')
      | Fn_d f ks xs e =>
        p <- malloc (Closure_v env xs e) ;;
        ret (extend env f p)
      | Prim_d x p vs => 
        vs' <- mapM (eval_op env) vs ;;
        v <- eval_primop p vs' ;;
        ret (extend env x v)
      | Bind_d x w m vs => 
        vs' <- mapM (eval_op env) vs ;;
        sideEffect m vs' ;;
        ret env (** TODO **)
        
(*
      | Rec_d ds => 
        env' <- mapM malloc_dummy ds ; 
        _ <- mapM (initialize_decl (env' ++ env)) ds ; 
        ret (env' ++ env)
*)
    end.

  Fixpoint eval_exp (n:nat)(env:alist var value) (e:exp) : m (list value) := 
    match n with 
      | 0 => raise "out of gas"
      | S n => 
        match e with 
          | App_e v ks vs => 
            v' <- eval_op env v ;;
            vs' <- mapM (eval_op env) vs ;;
            match v' with 
              | Ptr_v z => 
                hv <- heap_lookup z ;;
                match hv with 
                  | Closure_v env xs e =>
                    env' <- extends env xs vs' ;; eval_exp n env' e
                  | _ => raise "applying non-function"
                end
              | _ => raise "applying non-function" 
            end
          | Let_e d e =>
            env' <- eval_decl env d ;;
            eval_exp n env' e
          | Letrec_e ds e => raise "TODO"
          | Switch_e v arms def => 
            v' <- eval_op env v ;;
            e <- find_arm v' arms def ;;
            eval_exp n env e
          | Halt_e o w => x <- eval_op env o ;; ret (x::nil)
          | AppK_e _ _ => raise "TODO"
          | LetK_e _ _ => raise "TODO"
        end 
    end.

  Definition run {A} (c : m A) (h:heap) : string + (A * heap * list (mop * list value)) :=
    runStateT (runStateT c h) nil.

  Definition eval (n:nat) (e:exp) : string + (list value * heap * list (mop * list value)) := 
    run (eval_exp n nil e) nil.

(*    
    Section TEST_EVAL.
      Import LambdaNotation. 
      Require Import ExtLib.Programming.Show.
      Local Open Scope string_scope.

      Eval compute in to_string (CPS (gen ((\x => x) @ Z_c))).
      Eval compute in eval 100 (CPS (gen ((\x => x) @ Z_c))).

      Eval compute in exp2string (CPS (gen e1)).
      Eval compute in eval 100 (CPS (gen e1)).

      Eval compute in exp2string (CPS (gen e2)).
      Eval compute in eval 100 (CPS (gen e2)).

      Eval compute in exp2string (CPS (gen e3)).
      Eval compute in eval 100 (CPS (gen e3)).

      Eval compute in exp2string (CPS (gen e4)).
      Eval compute in eval 100 (CPS (gen e4)).  (** Evalutes to None in 100 steps because it diverges *)

      Eval compute in exp2string (CPS (gen e5)).
      Eval compute in eval 100 (CPS (gen e5)).  
      
      Eval compute in exp2string (CPS (gen e6)).
      Eval compute in eval 100 (CPS (gen e6)).

      Eval compute in exp2string (CPS (gen e7)).
      Eval compute in eval 100 (CPS (gen e7)).

      Eval compute in exp2string (CPS (gen e8)).
      Eval compute in eval 100 (CPS (gen e8)).
    End TEST_EVAL.
    *)
End CPSEVAL.

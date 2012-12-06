Require Import List String.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsK CoqCompile.Env.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Programming.Show.
Require Import ZArith.
Require Import ExtLib.Data.Strings.

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
  
  Definition val2str (v:value) : string :=
    match v with
      | Con_v c => "Con(" ++ c ++ ")" 
      | Int_v z => match z with
                     | Z0 => "0"
                     | Zpos p => nat2string10 (Pos.to_nat p)
                     | Zneg p => "-" ++ nat2string10 (Pos.to_nat p)
                   end
      | Ptr_v n => "Ptr(" ++ nat2string10 n ++ ")"
      | World_v => "World" 
    end.

  (** Allocated values *)
  Inductive heap_value : Type := 
  | Tuple_v : list value -> heap_value
  | Closure_v : alist (var + cont) value -> list cont -> list var -> exp -> heap_value.
  
  (** We'll just naively implement heaps as lists of heap values *)
  Definition heap := list heap_value.

  Definition m : Type -> Type := GFixT (stateT heap (stateT (list (mop * list value)) (sum string))).
  
  (** We'll be working in a combination of the state and option monads, so
     I've written various environment and other functions tailored to that
     monad. *)
  Definition lookup {A} (env:alist (var + cont) A) (x:var + cont) : m A := 
    match Maps.lookup x env with
      | None => raise ("unknown variable " ++ to_string x)
      | Some v => ret v
    end.

  Definition extend {A} (env:alist (var + cont) A) (x:var + cont) (v:A) : alist (var + cont) A := 
    Maps.add x v env.

  Fixpoint extends {A}(env:alist (var + cont) A) (xs:list (var + cont)) (vs:list A) : m (alist (var + cont) A) := 
    match xs, vs with 
      | nil, nil => ret env
      | x::xs, v::vs => extends (extend env x v) xs vs
      | _, _ => raise "calling function with wrong # of arguments"
    end.

  Definition eval_op (env:alist (var + cont) value) (v:op) : m value := 
    match v with 
      | Con_o c => ret (Con_v c)
      | Int_o i => ret (Int_v i)
      | Var_o x => lookup env (inl x)
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
      | Eq_p, (Int_v i)::(Int_v j)::nil => ret (if eq_dec i j then (Con_v "True") else (Con_v "False"))
      | Eq_p, (Con_v i)::(Con_v j)::nil => ret (if eq_dec i j then (Con_v "True") else (Con_v "False"))
      | Neq_p, (Int_v i)::(Int_v j)::nil => ret (if eq_dec i j then (Con_v "False") else (Con_v "True"))
      | Neq_p, (Con_v i)::(Con_v j)::nil => ret (if eq_dec i j then (Con_v "False") else (Con_v "True"))
      | Lt_p, (Int_v i)::(Int_v j)::nil => ret (if Z.ltb i j then (Con_v "True") else (Con_v "False"))
      | Lte_p, (Int_v i)::(Int_v j)::nil => ret (if orb (Z.ltb i j) (eq_dec i j) 
        then (Con_v "True") else (Con_v "False"))
      | Ptr_p, ((Int_v _)::nil) => ret (Con_v "False")
      | Ptr_p, ((Con_v _)::nil) => ret (Con_v "False")
      | Ptr_p, ((Ptr_v _)::nil) => ret (Con_v "True")
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
      | _, _ => 
        let pop := to_string p in
        let args := fold_left (fun acc v => acc ++ val2str v ++ ", ") vs "" in
        raise ("bad primitive application of: " ++ pop ++ " to " ++ args)%string
    end.

    (** Used for initializing variables to some pointer value to a dummy
       heap value in a circular set of definitions. *)
  Definition malloc_dummy (d:decl) : m ((var + cont) * value) := 
    match d with 
      | Fn_d f ks _ _ => v <- malloc (Tuple_v nil) ;; ret (inl f,v)
      | Prim_d x MkTuple_p _ => 
        v <- malloc (Tuple_v nil) ;; 
        ret (inl x,v)
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
  Definition initialize_decl (env:alist (var + cont) value) (d: decl) : m unit :=
    match d with 
      | Fn_d f ks xs e => 
        v <- lookup env (inl f) ;;
        match v with 
          | Ptr_v n => heap_set n (Closure_v env ks xs e)
          | _ => raise "??"
        end
      | Prim_d x MkTuple_p vs => 
        vs' <- mapM (eval_op env) vs ;;
        v <- lookup env (inl x) ; 
        match v with 
          | Ptr_v n => heap_set n (Tuple_v vs')
          | _ => raise "??"
        end
      | _ => raise "??"
    end.

  Definition sideEffect (mo : mop) (ls : list value) : m unit :=
    modify (T := list (mop * list value)) (fun x => List.app x ((mo, ls) :: nil)) ;;
    ret tt.

  Fixpoint eval_decl (env:alist (var + cont) value) (d:decl) : m (alist (var + cont) value) := 
    match d with 
      | Op_d x v =>
        v' <- eval_op env v ;;
        ret (extend env (inl x) v')
      | Fn_d f ks xs e =>
        p <- malloc (Closure_v env ks xs e) ;;
        ret (extend env (inl f) p)
      | Prim_d x p vs => 
        vs' <- mapM (eval_op env) vs ;;
        v <- eval_primop p vs' ;;
        ret (extend env (inl x) v)
      | Bind_d x w m vs => 
        vs' <- mapM (eval_op env) vs ;;
        sideEffect m vs' ;;
        ret env (** TODO **)
    end.

  Definition eval_cont (env:alist (var + cont) value) (k:cont) : m value :=
    v <- lookup env (inr k) ;;
    ret v.

  Definition malloc_dummyk (k_xs_e:cont * list var * exp) : m ((var + cont) * value) := 
    let '(k, _, _) := k_xs_e in
    v <- malloc (Tuple_v nil) ;;
    ret (inr k, v).

  Definition initialize_declk (env:alist (var + cont) value) (k_xs_e:cont * list var * exp) : m unit :=
    let '(k, xs, e) := k_xs_e in
    match Maps.lookup (inr k) env with
      | Some (Ptr_v n) => heap_set n (Closure_v env nil xs e)
      | _ => raise "??"
    end.

  Definition eval_exp (env:alist (var + cont) value) (e:exp) : m (list value) :=
    mfix2 _ (fun recur => fix eval_exp (env:alist (var + cont) value) (e:exp) {struct e} : m (list value) :=
      match e with 
        | App_e v ks os => 
          v' <- eval_op env v ;;
          vs' <- mapM (eval_op env) os ;;
          vk' <- mapM (eval_cont env) ks ;;
          let _ : list value := vs' in
          let _ : list value := vk' in
          match v' with 
            | Ptr_v z => 
              hv <- heap_lookup z ;;
              match hv with 
                | Closure_v env kvs xs e =>
                  env' <- extends env (map (fun x => inl x) xs) vs' ;;
                  env' <- extends env' (map (fun x => inr x) kvs) vk' ;; 
                  recur env' e
                | _ => raise "applying non-function"
              end
            | _ => raise "applying non-function" 
          end
        | Let_e d e =>
          env' <- eval_decl env d ;;
          eval_exp env' e
        | Letrec_e ds e =>
          env' <- mapM malloc_dummy ds ;;
          let _ : alist (var + cont) value := env' in
          iterM (initialize_decl (env' ++ env)%list) ds ;;
          eval_exp (env' ++ env)%list e
        | Switch_e v arms def => 
          v' <- eval_op env v ;;
          e <- find_arm v' arms def ;;
          recur env e
        | Halt_e o w => x <- eval_op env o ;; ret (x::nil)
        | AppK_e k os =>
          vs <- mapM (eval_op env) os ;;
          v <- eval_cont env k ;;
          match v with
            | Ptr_v z =>
              hv <- heap_lookup z ;;
              match hv with
                | Closure_v env ks xs e => 
                  kvs <- mapM (eval_cont env) ks ;;
                  env' <- extends env (map (fun x => inl x) xs) vs ;;
                  env' <- extends env' (map (fun x => inr x) ks) kvs ;;
                  recur env' e
                | _ => raise "applying non-function (continuation case)"
              end
            | _ => raise "applying non-function (continuation case)"
          end
        | LetK_e k_xs_e e =>
          env' <- mapM malloc_dummyk k_xs_e ;;
          iterM (initialize_declk (env' ++ env)%list) k_xs_e ;;
          eval_exp (env' ++ env)%list e
      end) env e.

  Definition run {A} (n:N) (c : m A) (h:heap) : string + (A * heap * list (mop * list value)) :=
    match runStateT (runStateT (runGFixT c n) h) nil with
      | inl err => inl err
      | inr (None,_,_) => inl "Out of fuel"%string
      | inr (Some x,y,z) => inr (x,y,z)
    end.

  Definition eval (n:N) (e:exp) : string + (list value * heap * list (mop * list value)) := 
    run n (eval_exp nil e) nil.

  Require Import CoqCompile.Parse.
  Require Import CoqCompile.CpsKConvert.
  Require CoqCompile.CloConvK.

  Definition cloconv (e : exp) : string + exp :=
    match CloConvK.ClosureConvert.cloconv_exp e with
      | inl err => inl err
      | inr (ds,e) => inr (Letrec_e ds e)
    end.

  Definition evalstr (n:N) (io cc : bool) (s:string) : string + (list value * heap * list (mop * list value)) := 
    parse <- Parse.parse_topdecls s ;;
    let cps := if io then CPS_pure parse else CPS_io parse in
    let program := if cc then cloconv cps else inr cps in
    match program with
      | inl err => inl err
      | inr exp => eval n exp
    end.

  (*
    Section TEST_EVAL.
      Import LambdaNotation. 
      Require Import ExtLib.Programming.Show.
      Require Import CoqCompile.CpsKConvert.
      Local Open Scope string_scope.

      Eval vm_compute in to_string (CPS_pure (gen ((\x => x) @ Z_c))).
      Eval vm_compute in eval 100 (CPS_pure (gen ((\x => x) @ Z_c))).

      Eval vm_compute in to_string (CPS_pure (gen e1)).
      Eval vm_compute in eval 100 (CPS_pure (gen e1)).

      Eval vm_compute in to_string (CPS_pure (gen e2)).
      Eval vm_compute in eval 100 (CPS_pure (gen e2)).

      Eval vm_compute in to_string (CPS_pure (gen e3)).
      Eval vm_compute in eval 100 (CPS_pure (gen e3)).

      Eval vm_compute in to_string (CPS_pure (gen e4)).
      Eval vm_compute in eval 100 (CPS_pure (gen e4)).  (** Evalutes to None in 100 steps because it diverges *)

      Eval vm_compute in to_string (CPS_pure (gen e5)).
      Eval vm_compute in eval 100 (CPS_pure (gen e5)).  

      Eval vm_compute in to_string (CPS_pure (gen e6)).
      Eval vm_compute in eval 100 (CPS_pure (gen e6)).

      Eval vm_compute in to_string (CPS_pure (gen e7)).
      Eval vm_compute in eval 100 (CPS_pure (gen e7)).

      Eval vm_compute in to_string (CPS_pure (gen e8)).
      Eval vm_compute in eval 100 (CPS_pure (gen e8)).

    End TEST_EVAL.
  *)

End CPSEVAL.

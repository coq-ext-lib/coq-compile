Require Import CoqCompile.Lambda.
Require Import CoqCompile.CpsK.
Require Import CoqCompile.CpsKUtil.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import List Bool ZArith String.

Set Implicit Arguments.
Set Strict Implicit.

Section cps_convert.
  Import Lambda CPSK.
  
  (** Partition pattern matching arms into three classes -- (1) those that are matching on 
     nullary constructors, (2) those matching on nary constructors for n > 0, (3) a default
     pattern that matches anything.  Used in match compilation below. *)
  Fixpoint partition' v (arms:list (Lambda.pattern * exp)) 
                        (constants:list (CpsCommon.pattern * exp))
                        (pointers:list (CpsCommon.pattern * exp)) :=
     match arms with 
       | nil => (rev constants, rev pointers, None)
       | (Lambda.Con_p c nil, e)::rest => partition' v rest ((CpsCommon.Con_p c,e)::constants) pointers
       | (Lambda.Con_p c xs, e)::rest => 
         partition' v rest constants ((CpsCommon.Con_p c,bind_proj v xs 1 e)::pointers)
       | (Lambda.Var_p x,e)::rest => (rev constants, rev pointers, Some (Let_e (Op_d x v) e))
     end.

  Definition partition v arms := partition' v arms nil nil.
  
  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {State_m : MonadState positive m}.
    Import MonadNotation.
    Local Open Scope monad_scope.
    Local Open Scope string_scope.
    
  (** Generate a fresh variable **)
  Definition freshVar (s:option string) : m var := 
    n <- modify Psucc ;;
    ret (Env.mkVar s n).

  (** Generate a fresh variable **)
  Definition freshCont (s:string) : m cont := 
    n <- modify Psucc ;;
    ret (K s n).
  

  (** Convert a [Lambda.exp] into a CPS [exp].  The meta-level continuation [k] is used
      to build the "rest of the expression".  We work in the state monad so we can generate
      fresh variables.  In general, functions are changed to take an extra argument which
      is used as the object-level continuation.  We "return" a value [v] by invoking this
      continuation on [v]. 

      We also must lower Lambda's [Match_e] into CPS's simple Switch.  We are assuming 
      nullary constructors are represented as "small integers" that can be distinguished 
      from pointers, and that nary constructors are represented as pointers to tuples that 
      contain the constructor value in the first field, and the arguments to the 
      constructors in successive fields.  So for instance, [Cons hd tl] will turn into:
      [mkTuple_p [Cons, hd, tl]].  

      To do a pattern match on [v], we first test to see if [v] is a pointer.  If not,
      then we then use a [Switch_e] to dispatch to the appropriate nullary constructor case.
      If [v] is a pointer, then we extract the construtor tag from the tuple that v
      references.  We then [Switch_e] on that tag to the appropriate nary constructor
      case.  The cases then extract the other values from the tuple and bind them to
      the appropriate pattern variables.  
  *)
  Fixpoint cps (e:Lambda.exp) (k:op -> m exp) : m exp := 
    match e with 
      | Lambda.Var_e x => k (Var_o x)
      | Lambda.Con_e c nil => k (Con_o c)
      | Lambda.App_e e1 e2 => 
        cps e1 (fun v1 => 
          cps e2 (fun v2 => 
            a <- freshVar (Some "a") ;; 
            e <- k (Var_o a) ;;
(*
            match match_eta a e with
              | None => 
*)
                f <- freshCont "f" ;; 
                ret (LetK_e ((f, a::nil, e) :: nil) (App_e v1 (f::nil) (v2::nil)))
(*
              | Some c => ret (App_e v1 (v2::c::nil))
            end
            *)
          ))
      | Lambda.Con_e c es => 
        (fix cps_es (es:list Lambda.exp) (vs:list op)(k:list op -> m exp) : m exp := 
          match es with 
            | nil => k (rev vs)
            | e::es => cps e (fun v => cps_es es (v::vs) k)
          end) es nil
        (fun vs => 
          x <- freshVar (Some "x") ;;
          e <- k (Var_o x) ;;
          ret (Let_e (Prim_d x MkTuple_p ((Con_o c)::vs)) e))
      | Lambda.Let_e x e1 e2 => 
        cps e1 (fun v1 => 
          e2' <- cps e2 k ; 
          ret (Let_e (Op_d x v1) e2'))
      | Lambda.Lam_e x e => 
        f <- freshVar (Some "f") ;; 
        c <- freshCont "K" ;; 
        e' <- cps e (fun v => ret (AppK_e c (v::nil))) ; 
        e0 <- k (Var_o f) ; 
        ret (Let_e (Fn_d f (c::nil) (x::nil) e') e0)
      | Lambda.Letrec_e fs e => 
        fs' <- mapM (fun fn => 
          match fn with 
            | (f,(x,e)) => 
              c <- freshCont "c" ;; 
              e' <- cps e (fun v => ret (AppK_e c (v::nil))) ;;
              ret (Fn_d f (c::nil) (x::nil) e')
          end) fs ; 
        e0 <- cps e k ; 
        ret (Letrec_e fs' e0)
      | Lambda.Match_e e arms => 
        cps e (fun v => 
          x <- freshVar (Some "x") ;; 
          e0 <- k (Var_o x) ; 
          c <- freshCont "c" ;; 
(*          cont <- match match_eta x e0 with
                    | None => ret (Var_o c)
                    | Some v' => ret v'
                  end ;
*)
          arms' <- mapM (fun p_e => e' <- cps (snd (p_e)) (fun v => ret (AppK_e c (v::nil))) ;
            ret (fst p_e, e')) arms ; 
          is_ptr <- freshVar (Some "isptr") ;;
          tag <- freshVar (Some "tag") ;; 
          m <- match partition v arms' with 
                 | (constant_arms, pointer_arms, def) => 
                   ret (Let_e (Prim_d is_ptr Ptr_p (v::nil))
                     (Switch_e (Var_o is_ptr)
                       ((CpsCommon.Con_p "false"%string, switch_e v constant_arms def)::
                         (CpsCommon.Con_p "true"%string, 
                           (Let_e (Prim_d tag Proj_p ((Int_o 0)::v::nil))
                             (switch_e (Var_o tag) pointer_arms def)))::nil) None))
               end ;;
          ret (LetK_e ((c, (x::nil), e0) :: nil) m))
    end.

  End monadic.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Require Import CoqCompile.CpsKIO.

  Definition CPS_pure (e:Lambda.exp) : exp := 
    evalState (let w := InitWorld_o in
               cps e (fun x => ret (Halt_e x w))) 1%positive.

  Definition CPS_io (e:Lambda.exp) : exp :=
    let result := 
      evalState (cps e (fun x => ret (IO.runIO x))) 1%positive
    in IO.wrapIO (wrapVar "$__IO_bind__") (wrapVar "$__IO_return__") (wrapVar "$__IO_printint__") result.

End cps_convert.

(*
  Section CPSEVAL.
    (** Because this version of CPS supports recursive records, as well as recursive
        functions, I've chosen to use an allocation-style semantics here, where large
        values, such as tuples and closures, are allocated on a heap.  Then, to build
        circular values, such as recursive closures or recursive tuples, we first 
        allocate space for them, then initialize them with back-patching. *)

    (** Small values *)
    Inductive value : Type := 
    | Con_v : constructor -> value
    | Int_v : Z -> value
    | Ptr_v : nat -> value.

    (** Allocated values *)
    Inductive heap_value : Type := 
    | Tuple_v : list value -> heap_value
    | Closure_v : env_t value -> list var -> exp -> heap_value.

    (** We'll just naively implement heaps as lists of heap values *)
    Definition heap := list heap_value.

    (** We'll be working in a combination of the state and option monads, so
        I've written various environment and other functions tailored to that
        monad. *)
    Fixpoint lookup {A} (env:env_t A) (x:var) : optionT (state heap) A := 
      match env with 
        | nil => mzero
        | (y,v)::rest => if eq_dec y x then ret v else lookup rest x 
      end.

    Definition extend {A} (env:env_t A) (x:var) (v:A) : env_t A := (x,v)::env.

    Fixpoint extends {A}(env:env_t A) (xs:list var) (vs:list A) : optionT (state heap) (env_t A) := 
      match xs, vs with 
        | nil, nil => ret env
        | x::xs, v::vs => extends (extend env x v) xs vs
        | _, _ => mzero
      end.

    Definition eval_op (env:env_t value) (v:op) : optionT (state heap) value := 
      match v with 
        | Con_o c => ret (Con_v c)
        | Int_o i => ret (Int_v i)
        | Var_o x => lookup env x
      end.

    (** Find the appropriate switch arm for a given small value. *)
    Fixpoint find_arm (v:value) (arms : list (pattern * exp)) (def:option exp) : optionT (state heap) exp := 
      match v,arms with 
        | _,nil => match def with | None => mzero | Some e => ret e end
        | Con_v c, ((Con_p c',e)::rest) => if eq_dec c c' then ret e else find_arm v rest def
        | Int_v i, ((Int_p i',e)::rest) => if eq_dec i i' then ret e else find_arm v rest def
        | _,(_::rest) => find_arm v rest def
      end.

    (** Allocate a heap value and return its address as a pointer *)
    Definition malloc(v:heap_value) : optionT (state heap) value := 
      h <- get ;
      put (h ++ (v::nil)) ;; 
      ret (Ptr_v (List.length h)).

    (** Lookup the pointer [n] in the heap. *)
    Definition heap_lookup (n:nat) : optionT (state heap) heap_value := 
      h <- get ; 
      match nth_error h n with 
        | None => mzero
        | Some v => ret v
      end.

    Fixpoint heap_upd (n:nat) (h:heap) (v:heap_value) : option heap := 
      match n, h with 
        | 0, _::tail => ret (v::tail)
        | S n, head::tail => t <- (heap_upd n tail v) ; ret (head::t)
        | _, _ => None
      end.

    (** Update the heap value at location [n] to be the value [v]. *)
    Definition heap_set (n:nat) (v:heap_value) : optionT (state heap) unit := 
      h <- get ; 
      match heap_upd n h v with 
        | None => mzero
        | Some h' => put h'
      end.

    (** Evaluate the primops given closed values *)      
    Definition eval_primop (p:primop) (vs: list value) : optionT (state heap) value := 
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
                | None => mzero
                | Some v => ret v
              end
            | _ => mzero
          end
        | _, _ => mzero
      end%string.

    (** Used for initializing variables to some pointer value to a dummy
       heap value in a circular set of definitions. *)
    Definition malloc_dummy (d:decl) : optionT (state heap) (var * value) := 
      match d with 
        | Fn_d f _ _ => v <- malloc (Tuple_v nil) ; ret (f,v)
        | Prim_d x MkTuple_p _ => v <- malloc (Tuple_v nil) ; ret (x,v)
        | _ => mzero
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
    Definition initialize_decl(env:env_t value) (d: decl) : optionT (state heap) unit :=
      match d with 
        | Fn_d f xs e => 
          v <- lookup env f ; 
          match v with 
            | Ptr_v n => heap_set n (Closure_v env xs e)
            | _ => mzero
          end
        | Prim_d x MkTuple_p vs => 
          vs' <- mapM (eval_op env) vs ; 
          v <- lookup env x ; 
          match v with 
            | Ptr_v n => heap_set n (Tuple_v vs')
            | _ => mzero
          end
        | _ => mzero
      end.

    Fixpoint eval_decl (env:env_t value) (d:decl) : optionT (state heap) (env_t value) := 
      match d with 
        | Op_d x v => v' <- eval_op env v ; ret (extend env x v')
        | Fn_d f xs e => p <- malloc (Closure_v env xs e) ; ret (extend env f p)
        | Prim_d x p vs => vs' <- mapM (eval_op env) vs ; v <- eval_primop p vs' ; ret (extend env x v)
        | Rec_d ds => 
          env' <- mapM malloc_dummy ds ; 
          _ <- mapM (initialize_decl (env' ++ env)) ds ; 
          ret (env' ++ env)
      end.

    Fixpoint eval_exp (n:nat)(env:env_t value) (e:exp) : optionT (state heap) (list value) := 
      match n with 
        | 0 => mzero
        | S n => 
          match e with 
            | App_e v vs => 
              v' <- eval_op env v ; vs' <- mapM (eval_op env) vs ; 
              match v' with 
                | Ptr_v z => 
                  hv <- heap_lookup z ; 
                  match hv with 
                    | Closure_v env xs e => env' <- extends env xs vs' ; eval_exp n env' e
                    | _ => mzero
                  end
                | _ => mzero
              end
            | Let_e d e => env' <- eval_decl env d ; eval_exp n env' e
            | Switch_e v arms def => 
              v' <- eval_op env v ; e <- find_arm v' arms def ; eval_exp n env e
            | Halt_e o => x <- eval_op env o ;; ret (x::nil)
          end 
      end.

    Definition run {A} (c : optionT (state heap) A) (h:heap) : option A * heap := 
      runState (unOptionT c) h.

    Definition eval (n:nat) (e:exp) : option (list value) * heap := run (eval_exp n nil e) nil.

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
*)

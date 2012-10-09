Require Import Lambda.
Require Import ZArith String List Bool.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

(** Defines CPS language datatype, pretty printer, and conversion from Lambda.exp
    to the CPS language.
*)
Module CPS.
  Import MonadNotation. 
  Local Open Scope monad_scope.
  Definition var := Lambda.var.
  Definition constructor := Lambda.constructor.
  Definition env_t := Lambda.env_t.

  (** Operands are "small" values (fit into a register) and include variables, 
      zero-arity constructors (e.g., true, false, nil) and integers. *)
  Inductive op : Type := 
  | Var_o : var -> op
  | Con_o : constructor -> op
  | Int_o : Z -> op.

  (** We compile pattern matching into simple C-like switch expressions, where
      you can only match an operand against a tag, which is either an integer
      or symbolic constructor tag. *)
  Inductive pattern : Type := 
  | Int_p : Z -> pattern
  | Con_p : constructor -> pattern.

  (** We have a bunch of primitive operations on values *)
  Inductive primop : Type := 
  (* comparisons/tests *) 
  | Eq_p     (* operand equality *)
  | Neq_p    (* operand inequality *)
  | Lt_p     (* integer less than *)
  | Lte_p    (* integer ltess than or equal *)
  | Ptr_p    (* is the value a pointer?  used to distinguish nullary constructors *)
  (* arithmetic *)
  | Plus_p   (* we don't include division as it's partial *)
  | Minus_p 
  | Times_p
  (* build tuple and projection from a tuple *)
  | MkTuple_p (* mkTuple_p [v1;...;vn] builds a record of n words and initializes it 
                 with the values v1,...,vn. *)
  | Proj_p.   (* Proj_p [Int_o i;v] projects the ith component of the tuple referenced
                 by v, using zero-based indexing. *)

  (** CPS are in general a sequence of let-bindings that either terminate with 
      a function application, or else fork using a switch into a tree of nested
      CPS expressions.  *)
  Inductive exp : Type := 
  | App_e : op -> list op -> exp
  | Let_e : decl -> exp -> exp
    (** Switch is only used on small integer values and unlike Match, doesn't do any
        pattern matching.  The optional expression at the end is a default in case
        none of the patterns matches the value. *)
  | Switch_e : op -> list (pattern * exp) -> option exp -> exp
  | Halt_e : op -> exp
  with decl : Type := 
    (** let x := v *)
  | Op_d : var -> op -> decl
    (** let x := p(v1,...,vn) *)
  | Prim_d : var -> primop -> list op -> decl
    (** let f := fun (x1,...,xn) => e *)
  | Fn_d : var -> list var -> exp -> decl
    (** let rec [d1;d2;...;dn].  Note that this is more general than we really need.
        What we need is letrec over both functions and over tuples (to support cyclic
        construction of data structures needed for recursive closures.)  In general,
        we will not have nested [Rec_d] declarations, and the nested declarations
        will either be a [Fn_d] or else a [Prim_d _ MkTuple_p]. *)
  | Rec_d : list decl -> decl.

  (** Pretty printing CPS expressions *)
  Section PP.
    Local Open Scope string_scope.

    Definition pos2string(p:positive) := LambdaNotation.nat2string (Pos.to_nat p).
    Fixpoint spaces (n:nat) : string :=
      match n with
        | 0 => ""
        | S n => " " ++ (spaces n)
      end.

    Definition emit (s:string) : state (list string) unit :=
      sofar <- get ; put (s::sofar).
    
    Fixpoint indent (n:nat) : state (list string) unit :=
      match n with
        | 0 => ret tt
        | S n => emit " " ;; indent n
      end.

    Fixpoint emit_list{A}(f:A->string)(vs:list A) : state (list string) unit :=
      match vs with
        | nil => ret tt
        | v::nil => emit (f v)
        | v::vs => emit (f v) ;; emit "," ;; emit_list f vs
      end.

    Definition newline : string := (String (Ascii.ascii_of_nat 10) EmptyString).

    Section ITER.
      Context {S A:Type}.
      Variable f : A -> state S unit.
      
      Fixpoint iter (xs:list A) : state S unit :=
        match xs with
          | nil => ret tt
          | h::t => f h ;; iter t
        end.
    End ITER.

    Definition z2string(x:Z) : string := 
      match x with 
        | Z0 => "0"
        | Zpos p => pos2string p
        | Zneg p => "-" ++ (pos2string p)
      end.
    Definition op2string (v:op) : string := 
      match v with 
        | Var_o x => x
        | Con_o c => "Con(" ++ c ++ ")"
        | Int_o i => z2string i
      end.
    Definition pat2string (p:pattern) : string := 
      match p with 
        | Int_p i => z2string i
        | Con_p c => c
      end.
    Definition primop2string (p:primop) : string := 
      match p with 
        | Eq_p => "eq?"
        | Neq_p => "neq?"
        | Lt_p => "lt?"
        | Lte_p => "lte?"
        | Ptr_p => "ptr?"
        | Plus_p => "+"
        | Minus_p => "-"
        | Times_p => "*"
        | Proj_p => "#"
        | MkTuple_p => "mkTuple"
      end.

     Fixpoint emitexp (n:nat)(e:exp) : state (list string) unit := 
       emit newline ;; indent n ;;
       match e with 
         | App_e v vs => emit (op2string v) ;; emit "(" ;; emit_list op2string vs ;; emit ")" 
         | Let_e d e => 
           emit "let ";; emitdecl false (2+n) d ;; emitexp (2+n) e 
         | Switch_e v arms def => 
           emit "switch ";; emit (op2string v) ;; emit " with" ;; 
           iter (fun (p: pattern * exp) => 
             emit newline ;; indent n ;; emit "| ";; emit (pat2string (fst p)) ;; emit " => ";; 
             emitexp (2+n) (snd p)) arms ;;
           match def with 
             | None => ret tt 
             | Some e => emit newline ;; indent n ;; emit "| _ => " ;; emitexp (2+n) e
           end ;;
           emit newline ;; indent n ;; emit "end"
         | Halt_e o => emit "HALT " ;; emit (op2string o)
       end
     with emitdecl (inrec:bool)(n:nat)(d:decl) : state (list string) unit := 
       let emit_sep : state (list string) unit := if inrec then emit " and" else emit " in" in 
       match d with 
         | Op_d x v => 
           emit x ;; emit " = " ;; emit (op2string v) ;; emit_sep 
         | Prim_d x p vs => 
           emit x ;; emit " = " ;; emit (primop2string p) ;; emit "(" ;; 
           emit_list op2string vs ;; emit ")" ;; emit_sep 
         | Fn_d f xs e => 
           emit f ;; emit "(" ;; emit_list (fun x => x) xs ;; emit ") = " ;; 
           emitexp (2+n) e ;; emit_sep 
         | Rec_d ds => 
           emit "rec ";; 
           let iter_sep := 
             fix iter_sep(ds:list decl) : state (list string) unit := 
             match ds with 
               | nil => emit_sep
               | d::nil => emitdecl inrec (2+n) d 
               | d::ds => emitdecl true (2+n) d ;; emit newline ;; indent n ;; iter_sep ds 
             end
             in
             iter_sep ds
       end.

     Definition exp2string(e:exp) : string := 
       List.fold_left (fun x y => y ++ x) (snd (runState (emitexp 0 e) nil)) "".
  End PP.

  Global Instance RelDec_Z_eq : RelDec (@eq Z) := 
  { rel_dec := Zeq_bool }.

  Global Instance RelDecCorrect_Z_eq : RelDec_Correct RelDec_Z_eq.
  Proof.
    constructor. intros.  generalize (Zeq_is_eq_bool x y). simpl. intros. tauto.
  Qed.

  Global Instance RelDec_primop_eq : RelDec (@eq primop) := 
  { rel_dec := fun x y =>
    match x , y with
      | Eq_p , Eq_p 
      | Neq_p , Neq_p
      | Lt_p , Lt_p
      | Lte_p , Lte_p
      | Ptr_p , Ptr_p
      | Plus_p , Plus_p
      | Minus_p , Minus_p
      | Times_p , Times_p
      | MkTuple_p , MkTuple_p 
      | Proj_p , Proj_p => true
      | _ , _ => false
    end }.

  Global Instance RelDecCorrect_primop_eq : RelDec_Correct RelDec_primop_eq.
  Proof.
    constructor. destruct x; destruct y; simpl; split; intros; subst; try congruence.
  Qed.

  Global Instance RelDec_op_eq : RelDec (@eq op) :=
  { rel_dec l r := match l , r with
                     | Var_o l , Var_o r => eq_dec l r
                     | Con_o l , Con_o r => eq_dec l r
                     | Int_o l , Int_o r => eq_dec l r
                     | _ , _ => false
                   end }.

  Global Instance RelDecCorrect_op_eq : RelDec_Correct RelDec_op_eq.
  Proof.
    constructor. destruct x; destruct y; simpl; split; intros; subst; try congruence ; 
    try ((consider (string_dec v v0) || consider (string_dec c c0))) ; intros ; subst; 
      try congruence ; generalize (Zeq_is_eq_bool z z0) ; intros ;destruct H0. rewrite (H1 H). auto.
    injection H ; intros ; subst. auto.
  Qed.

  (** returns the function name f if [fun x => e] is a simple eta expansion of the form
     [fun x => f x]. *)
  Definition match_eta (x:var) (e:exp) : option op := 
    match e with 
      | App_e op1 ((Var_o y)::nil) => 
        if eq_dec y x then Some op1 else None
      | _ => None
    end.
  
  Fixpoint eq_vars_ops (xs:list var) (vs:list op) : bool := 
    match xs, vs with 
      | nil, nil => true
      | x::xs, (Var_o y)::vs => eq_dec x y && eq_vars_ops xs vs
      | _, _ => false
    end.
  
  (** similar to the above, but for the general case of [fun (x1,...,xn) => e] being an
     eta-expansion of [fun (x1,...,xn) => f(x1,...,xn)]. *)
  Definition match_etas (xs:list var) (e:exp) : option op := 
    match e with 
      | App_e op1 ys =>
        if eq_vars_ops xs ys then Some op1 else None
      | _ => None
    end.
  
  (** Let-bind [xi] to [#i v] for the expression [e].  This is used in the compilation
      of pattern matching below. *)
  Fixpoint bind_proj(v:op)(xs:list var)(offset:Z)(e:exp) : exp := 
    match xs with 
      | nil => e
      | x::xs => Let_e (Prim_d x Proj_p ((Int_o offset)::v::nil)) (bind_proj v xs (1+offset) e)
    end.
  
  (** Partition pattern matching arms into three classes -- (1) those that are matching on 
     nullary constructors, (2) those matching on nary constructors for n > 0, (3) a default
     pattern that matches anything.  Used in match compilation below. *)
  Fixpoint partition' v (arms:list (Lambda.pattern * exp)) 
                        (constants:list (pattern * exp))
                        (pointers:list (pattern * exp)) :=
     match arms with 
       | nil => (rev constants, rev pointers, None)
       | (Lambda.Con_p c nil, e)::rest => partition' v rest ((Con_p c,e)::constants) pointers
       | (Lambda.Con_p c xs, e)::rest => 
         partition' v rest constants ((Con_p c,bind_proj v xs 1 e)::pointers)
       | (Lambda.Var_p x,e)::rest => (rev constants, rev pointers, Some (Let_e (Op_d x v) e))
     end.

  Definition partition v arms := partition' v arms nil nil.
  
  (** Generate a fresh variable -- assumes no user-level variables start with "$". *)
  Definition freshVar(s:string) : state nat string := LambdaNotation.fresh ("$"%string ++ s).
  
  (** Simplify a switch that only has one branch. *)
  Definition SimplSwitch_e (v:op) (arms: list (pattern * exp)) (def:option exp) := 
    match arms, def with 
      | (p,e)::nil, None => e
      | _, _ => Switch_e v arms def
    end.

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
  Fixpoint cps(e:Lambda.exp)(k:op -> state nat exp) : state nat exp := 
    match e with 
      | Lambda.Var_e x => k (Var_o x)
      | Lambda.Con_e c nil => k (Con_o c)
      | Lambda.App_e e1 e2 => 
        cps e1 (fun v1 => 
          cps e2 (fun v2 => 
            a <- freshVar "a" ; 
            e <- k (Var_o a) ; 
            match match_eta a e with
              | None => 
                f <- freshVar "f" ; 
                ret (Let_e (Fn_d f (a::nil) e) (App_e v1 (v2::(Var_o f)::nil)))
              | Some c => ret (App_e v1 (v2::c::nil))
            end))
      | Lambda.Con_e c es => 
        (fix cps_es (es:list Lambda.exp) (vs:list op)(k:list op -> state nat exp) : state nat exp := 
          match es with 
            | nil => k (rev vs)
            | e::es => cps e (fun v => cps_es es (v::vs) k)
          end) es nil
        (fun vs => 
          x <- freshVar "x" ; 
          e <- k (Var_o x) ; 
          ret (Let_e (Prim_d x MkTuple_p ((Con_o c)::vs)) e))
      | Lambda.Let_e x e1 e2 => 
        cps e1 (fun v1 => 
          e2' <- cps e2 k ; 
          ret (Let_e (Op_d x v1) e2'))
      | Lambda.Lam_e x e => 
        f <- freshVar "f" ; 
        c <- freshVar "c" ; 
        e' <- cps e (fun v => ret (App_e (Var_o c) (v::nil))) ; 
        e0 <- k (Var_o f) ; 
        ret (Let_e (Fn_d f (x::c::nil) e') e0)
      | Lambda.Letrec_e fs e => 
        fs' <- mapM (fun fn => 
          match fn with 
            | (f,(x,e)) => 
              c <- freshVar "c" ; 
              e' <- cps e (fun v => ret (App_e (Var_o c) (v::nil))) ; 
              ret (Fn_d f (x::c::nil) e')
          end) fs ; 
        e0 <- cps e k ; 
        ret (Let_e (Rec_d fs') e0)
      | Lambda.Match_e e arms => 
        cps e (fun v => 
          x <- freshVar "x" ; 
          e0 <- k (Var_o x) ; 
          c <- freshVar "c" ; 
          cont <- match match_eta x e0 with
                    | None => ret (Var_o c)
                    | Some v' => ret v'
                  end ;
          arms' <- mapM (fun p_e => e' <- cps (snd (p_e)) (fun v => ret (App_e cont (v::nil))) ;
            ret (fst p_e, e')) arms ; 
          is_ptr <- freshVar "isptr" ; 
          tag <- freshVar "tag" ; 
          m <- match partition v arms' with 
                 | (constant_arms, pointer_arms, def) => 
                   ret (Let_e (Prim_d is_ptr Ptr_p (v::nil))
                     (Switch_e (Var_o is_ptr)
                       ((Con_p "false"%string, SimplSwitch_e v constant_arms def)::
                         (Con_p "true"%string, 
                           (Let_e (Prim_d tag Proj_p ((Int_o 0)::v::nil))
                             (SimplSwitch_e (Var_o tag) pointer_arms def)))::nil) None))
               end ; 
          match match_eta x e0 with 
            | None => ret (Let_e (Fn_d c (x::nil) e0) m)
            | Some _ => ret m
          end
          )
    end.

  Definition CPS(e:Lambda.exp) : exp := 
    fst (runState (cps e (fun x => ret (Halt_e x))) 0).

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
        | nil => zero
        | (y,v)::rest => if eq_dec y x then ret v else lookup rest x 
      end.

    Definition extend {A} (env:env_t A) (x:var) (v:A) : env_t A := (x,v)::env.

    Fixpoint extends {A}(env:env_t A) (xs:list var) (vs:list A) : optionT (state heap) (env_t A) := 
      match xs, vs with 
        | nil, nil => ret env
        | x::xs, v::vs => extends (extend env x v) xs vs
        | _, _ => zero
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
        | _,nil => match def with | None => zero | Some e => ret e end
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
        | None => zero
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
        | None => zero
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
                | None => zero
                | Some v => ret v
              end
            | _ => zero
          end
        | _, _ => zero
      end%string.

    (** Used for initializing variables to some pointer value to a dummy
       heap value in a circular set of definitions. *)
    Definition malloc_dummy (d:decl) : optionT (state heap) (var * value) := 
      match d with 
        | Fn_d f _ _ => v <- malloc (Tuple_v nil) ; ret (f,v)
        | Prim_d x MkTuple_p _ => v <- malloc (Tuple_v nil) ; ret (x,v)
        | _ => zero
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
            | _ => zero
          end
        | Prim_d x MkTuple_p vs => 
          vs' <- mapM (eval_op env) vs ; 
          v <- lookup env x ; 
          match v with 
            | Ptr_v n => heap_set n (Tuple_v vs')
            | _ => zero
          end
        | _ => zero
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
        | 0 => zero
        | S n => 
          match e with 
            | App_e v vs => 
              v' <- eval_op env v ; vs' <- mapM (eval_op env) vs ; 
              match v' with 
                | Ptr_v z => 
                  hv <- heap_lookup z ; 
                  match hv with 
                    | Closure_v env xs e => env' <- extends env xs vs' ; eval_exp n env' e
                    | _ => zero
                  end
                | _ => zero
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
      Local Open Scope string_scope.

      Eval compute in exp2string (CPS (gen ((\x => x) @ Z_c))).
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

End CPS.

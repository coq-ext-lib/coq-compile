Require Import String.
Require Import List.

Class Monad(M:Type->Type) : Type := { 
  Return : forall {A:Type}, A -> M A ; 
  Bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.
Notation "'ret' x" := (Return x) (at level 75) : monad_scope.
Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2))
  (right associativity, at level 84, c1 at next level) : monad_scope.
Notation "[ x , y ] <- c1 ; c2" := 
  (Bind c1 (fun v => match v with | (x,y) => c2 end)) 
  (right associativity, at level 84) : monad_scope.

Instance OptionMonad : Monad option := {
  Return := fun A (x:A) => Some x ; 
  Bind := fun {A B:Type} (c:option A) (f:A -> option B) => 
            match c with | None => None | Some x => f x end
}.
Definition ST (state:Type) (A:Type) := state -> state * A.
Instance StateMonad(state:Type) : Monad (ST state) := {
  Return := fun {A} (x:A) (s:state) => (s,x) ; 
  Bind := fun {A B} (c:ST state A) (f:A -> ST state B) (s:state) => 
            match c s with | (s',x) => f x s' end
}.

Module Lambda.
  (** data constructors, such as "true", "false", "nil", "::", "0", "S", etc. *)
  Definition constructor := string.

  (** variables *)
  Definition var := string.

  (** environments -- naively as an association list *)
  Definition env_t A := list (var * A).

  Local Open Scope monad_scope.

  Fixpoint lookup {A} (env: env_t A) (x:var) : option A := 
    match env with 
      | nil => None
      | (y,v)::env' => if string_dec x y then ret v else lookup env' x
    end.

  (** Lambda has only very basic patterns (no nesting).  So we can only write
      matches such as:
      
         match e with 
         | C1 x1 x2 ... xn => e1
         | C2 y1 y2 ... yn => e2
         | ...
         | z => e

       We assume, or rather, Coq will guarantee, that the patterns are exhaustive
       and non-overlapping. *)
  Inductive pattern : Type := 
  | Con_p : constructor -> list var -> pattern
  | Var_p : var -> pattern.

  (** Expressions in Lambda include variables, functions (lambda-expressions over
      one variable), function applications, a basic sequential "let", a data
      constructor applied to arguments, a match expression, or a letrec.  The
      letrec binds a list of variables f1,...,fn to function definitions
      (fun x1 => e1) ... (fun xn => en) within the scope of some expression "e".
  *)
  Inductive exp : Type := 
  | Var_e : var -> exp
  | Lam_e : var -> exp -> exp
  | App_e : exp -> exp -> exp
  | Let_e : var -> exp -> exp -> exp
  | Con_e : constructor -> list exp -> exp
  | Match_e : exp -> list (pattern * exp) -> exp
  | Letrec_e : env_t (var * exp) -> exp -> exp.

  Section CBV_SEMANTICS.
  (** Here, we model evaluation of expressions to give a "formal" definition 
      of the meaning of programs.  Because [exp] includes the potential for
      diverging programs, we can't directly write the semantics as a Coq
      total function.  However, we can construct a predicate (relation)
      as a partial function between expressions and values. *)

  (** A value is the result of evaluating an expression.  A value is 
      either a data constructor applied to values (e.g., "true", or "true::nil"),
      or a closure.  We have two kinds of closures, one corresponding to
      non-recursive functions, and one corresponding to recursive functions.
      In both cases, the closure captures the environment (a mapping from 
      variables to values) along with the function definition.  To model
      recursion, we have to "unwind" the recursive definitions.  To avoid
      needing infinite (co-inductive) terms, we do this lazily at the 
      site of application.  So the [Fix_v] form of closure specifies
      an environment, a set of mutually-recursive functions (as in a letrec)
      and a particular function name [f] from the set of recursively
      defined functions.  That is, [Fix_v env [(f1,(x1,e1)),...,(fn,(xn,en))] fi]
      is morally equivalent to [letrec f1 x1 = e1 ... fn xn = en in fi]. *)
  Inductive value : Type := 
  | Con_v : constructor -> list value -> value
  | Closure_v : env_t value -> var -> exp -> value
  | Fix_v : env_t value -> env_t (var * exp) -> var -> value.

  Fixpoint zip {A B} (xs:list A) (ys:list B) : option (list (A * B)) := 
    match xs, ys with 
      | nil, nil => ret nil
      | x::xs, y::ys => t <- (zip xs ys) ; ret ((x,y)::t)
      | _, _ => None
    end.

  Fixpoint eval_n (n:nat) (env:env_t value) (e:exp) : option value := 
    match n with 
      | 0 => None
      | S n => 
        match e with 
          | Var_e x => lookup env x
          | Lam_e x e => ret (Closure_v env x e)
          | App_e e1 e2 => 
            v1 <- eval_n n env e1 ;
            v2 <- eval_n n env e2 ;
            match v1 with 
              | Closure_v env x e => eval_n n ((x,v2)::env) e
              | Fix_v env fs f => 
                let env' :=            
                  List.map 
                  (fun (p:var * (var * exp)) => let (f,_) := p in (f,Fix_v env fs f)) fs in
                  match lookup fs f with 
                    | None => None
                    | Some (x,e) => eval_n n ((x,v2)::env' ++ env) e
                  end
              | _ => None
            end
          | Con_e c es => 
            (fix map_eval_n (xs:list exp) (k:list value -> option value) : option value := 
              match xs with 
                | nil => k nil
                | e::es => v <- eval_n n env e ; map_eval_n es (fun vs => k (v::vs))
              end) 
            es (fun vs => ret (Con_v c vs))
          | Let_e x e1 e2 => 
            v1 <- eval_n n env e1 ; eval_n n ((x,v1)::env) e2
          | Letrec_e fs e => 
            let env' :=
              List.map 
              (fun (p:var * (var * exp)) => let (f,_) := p in (f,Fix_v env fs f)) fs in
              eval_n n (env' ++ env) e
          | Match_e e arms => 
            v <- eval_n n env e ; 
            match v with 
              | Con_v c vs => 
                (fix find_arm (arms:list (pattern * exp)) := 
                  match arms with 
                    | nil => None
                    | ((Var_p x),e)::arms => eval_n n ((x,v)::env) e
                    | ((Con_p c' xs),e)::arms => 
                      if string_dec c c' then 
                        env' <- zip xs vs ; eval_n n (env' ++ env) e
                      else find_arm arms
                  end) arms
              | _ => None
            end
        end
    end.

  Definition evals (env:env_t value) (e:exp) (v:value) : Prop := 
    exists n, eval_n n env e = Some v.

  End CBV_SEMANTICS.

  Section SYNTAX.
    Fixpoint even(m:nat) : bool := 
      match m with 
        | 0 => true
        | S 0 => false
        | S (S n) => even n
      end.
    Local Open Scope string_scope.
    Section Program_Scope.
    Require Import Program.
    Program Fixpoint nat2string (n:nat) {measure n}: string := 
      match n with 
        | 0 => "0"
        | S 0 => "1"
        | m => (nat2string (Arith.Div2.div2 m)) ++ (if even m then "0" else "1")
      end.
    Next Obligation. destruct n. congruence. 
      apply (Arith.Div2.lt_div2 (S n)). auto with arith.
    Defined.
    End Program_Scope.

    Definition fresh (x:string) : ST nat string := 
      fun n => (n+1, x ++ (nat2string n)).

    Definition Exp := ST nat exp.
    Definition gen (E : Exp) : exp := snd (E 0).
    Definition FN (f : Exp -> Exp) : Exp := 
      x <- fresh "x" ; e <- f (ret (Var_e x)) ; ret (Lam_e x e).
    Notation "\ x => e" := (FN (fun x => e)) (at level 80) : syntax_scope.
    Definition APP (E1 E2:Exp) : Exp := e1 <- E1 ; e2 <- E2 ; ret (App_e e1 e2).
    Notation "E1 @ E2" := (APP E1 E2) (left associativity, at level 69) : syntax_scope.
    Definition LET (E1:Exp) (f:Exp -> Exp) : Exp := 
      x <- fresh "x" ; e1 <- E1 ; e2 <- f (ret (Var_e x)) ; ret (Let_e x e1 e2).
    Notation "'def' x := E1 'in' E2" := (LET E1 (fun x => E2))
      (right associativity, at level 75, E2 at next level) : syntax_scope.
    Definition LETREC (f:Exp -> Exp -> Exp) (E:Exp -> Exp) : Exp := 
      fname <- fresh "f" ; x <- fresh "x" ; 
      fbody <- f (ret (Var_e fname)) (ret (Var_e x)) ; 
      e <- E (ret (Var_e fname)) ; 
      ret (Letrec_e ((fname,(x,fbody))::nil) e).
    Notation "'defrec' f [ x ] := E1 'in' E2" := (LETREC (fun f x => E1) (fun f => E2))
      (right associativity, at level 75, E2 at next level) : syntax_scope.
    Definition true_c : Exp := ret (Con_e "true" nil).
    Definition false_c : Exp := ret (Con_e "false" nil).
    Definition Z_c : Exp := ret (Con_e "0" nil).
    Definition S_c (E:Exp) : Exp := e <- E ; ret (Con_e "S" (e::nil)).
    Definition IF_e (E1 E2 E3:Exp) : Exp := 
      e1 <- E1 ; e2 <- E2 ; e3 <- E3 ; 
      ret (Match_e e1 ((Con_p "true" nil, e2)::(Con_p "false" nil, e3)::nil)).
    Notation "'If' E1 'then' E2 'else' E3" := (IF_e E1 E2 E3)
      (right associativity, at level 72, E3 at next level) : syntax_scope.
    Notation "'nat_match' E 'with' 'Z' => E1 | 'S' [ x2 ] => E2" := 
      (e <- E ; e1 <- E1 ; n <- fresh "n" ; e2 <- (fun x2 => E2) (ret (Var_e n)) ; 
        ret (Match_e e ((Con_p "0" nil, e1) :: (Con_p "S" (n::nil), e2) :: nil)))
      (at level 72, e2 at next level) : syntax_scope.
    Definition PAIR_e (E1 E2:Exp) : Exp := 
      e1 <- E1 ; e2 <- E2 ; ret (Con_e "pair" (e1::e2::nil)).
    Notation "[[ e1 , e2 ]]" := (PAIR_e e1 e2).
    Definition fst (E1:Exp) : Exp := 
     e1 <- E1 ; a <- fresh "a" ; b <- fresh "b" ; 
     ret (Match_e e1 ((Con_p "pair" (a::b::nil), Var_e a)::nil)).
    Definition snd (E1:Exp) : Exp := 
      e1 <- E1 ; a <- fresh "a" ; b <- fresh "b" ; 
      ret (Match_e e1 ((Con_p "pair" (a::b::nil), Var_e b)::nil)).
    
    Local Open Scope syntax_scope.
    Definition e1 := def y := S_c Z_c in S_c y.
    Definition e2 := \ x => def x := S_c x in S_c x.
    Definition e3 := \ f => \ x => f @ x.
    Definition e4 := defrec f[x] := f @ x in f @ Z_c.
    Definition e5 := (\ x => If x then Z_c else S_c Z_c) @ false_c.
    Definition e6 := nat_match S_c (S_c Z_c) with Z => Z_c | S [y] => y.
    Definition e7 := 
      defrec plus[n] := (\m => nat_match n with Z => m | S[p] => plus @ p @ (S_c m))
      in plus.
    Definition four := S_c (S_c (S_c (S_c Z_c))).
    Definition two := S_c (S_c Z_c).
    Definition p := [[ two , four ]].
    Definition two' := fst two.
    Definition e8 := 
      def compose := \f => \g => \x => g @ (f @ x) in
      def inc := \x => S_c x in
      defrec plus[n] := 
      nat_match n with 
        Z => \m => m
      | S[p] => compose @ (plus @ p) @ inc 
      in plus @ two.

   Eval compute in eval_n 20 nil (gen (e8 @ two)).

   End SYNTAX.
End Lambda.

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

  Local Open Scope monad_scope.
  Definition K (Ans A:Type) := (A -> ST nat Ans) -> ST nat Ans.
  Instance ContMonad(Ans:Type) : Monad (K Ans) := {
    Return := fun {A} (x:A) (k:A -> ST nat Ans) => k x ; 
    Bind := fun {A B} (c:K Ans A) (f: A -> K Ans B) (k : B -> ST nat Ans) => 
               c (fun v => f v k)
  }.

  Local Open Scope string_scope.
  Definition freshTemp {Ans} (x:string) : K Ans var := 
    fun k n => k ("$" ++ x ++ (Lambda.nat2string n)) (1+n).
  
  Definition plug (f : exp -> exp) (x : op) : K exp op := 
    fun k n => let (n',e) := k x n in (n', f e).
  Notation "f [[ x ]]" := (plug f x) 
    (at level 84).

  Definition LetLam_e (f:var) (xs: list var) (e:exp) (e':exp) := 
    Letrec_e ((f,(xs,e))::nil) e'.

  Definition match_eta (x:var) (e:exp) := 
    match e with 
      | App_e op1 ((Var_o y)::nil) => 
        if string_dec y x then Some op1 else None
      | _ => None
    end.

  Definition App_k (v1 v2:op) : K exp op := 
    a <- freshTemp "a" ; 
    f <- freshTemp "f" ; 
    fun k n => 
      let (n', e) := k (Var_o a) n in
        match match_eta a e with
          | None => (n', LetLam_e f (a::nil) e (App_e v1 (v2::(Var_o f)::nil)))
          | Some op => (n', App_e v1 (v2::op::nil))
        end.

  Definition run (e:K exp op) : K exp (var*exp) := 
    c <- freshTemp "c" ; 
    fun k n => 
      let (n', e') := e (fun v n => (n, App_e (Var_o c) (v::nil))) n in 
        k (c,e') n'.

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
        Let_e x c ops [[ Var_o x ]]
      | Lambda.Let_e x e1 e2 => 
        v1 <- cps e1 ;
        (fun k n => 
          let (n', e2') := cps e2 k n in
            (n', Match_e v1 ((Lambda.Var_p x, e2')::nil)))
      | Lambda.App_e e1 e2 => 
        v1 <- cps e1 ; v2 <- cps e2 ; App_k v1 v2
      | Lambda.Lam_e x e => 
        f <- freshTemp "f" ; 
        [c,e'] <- run (cps e) ; 
        LetLam_e f (x::c::nil) e' [[ Var_o f ]] 
      | Lambda.Letrec_e fs e => 
        fs' <- (fix cps_fns (fs:env_t (var*Lambda.exp)) (cpsfs:env_t (list var * exp)) : K exp (env_t (list var * exp)) := 
                match fs with 
                  | nil => ret (List.rev cpsfs)
                  | (f,(x,e))::fs' => 
                    [c,e'] <- run (cps e) ; cps_fns fs' ((f,(x::c::nil, e'))::cpsfs)
                end) fs nil ; 
        v <- cps e ; 
        Letrec_e fs' [[ v ]]  
      | Lambda.Match_e e arms =>  
        v <- cps e ; 
        c <- freshTemp "c" ; 
        x <- freshTemp "x" ; 
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
    end.

    Definition CPS (e:Lambda.exp) : exp := 
      snd (cps e (fun v n => (n, App_e (Var_o "halt") (v::nil))) 0).
End CPS.      
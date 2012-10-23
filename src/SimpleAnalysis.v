Require Import ZArith String Bool.
Require Import Cps.
Require Import ExtLib.Monad.Monad.
Require Import List.
Require Import ExtLib.Monad.StateMonad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.FMaps.FMapAList.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

(** Demonstrates a simple reaching-definition style analysis. 
    This is not very efficient because of the use of association
    lists for finite maps, and the use of lists as sets.  We 
    should use the better maps/sets provided by the library. 

    If we do that, then the worst-case complexity of the analysis is 
    roughly O(n^3 * lg n).  The lg n factor is due to the cost of
    doing inserts/updates/etc. on the functional sets/maps.  
    The n^3 factor is due to (1) there O(n) variables, (2) each
    variable can take up to O(n) iterations to reach a fixed
    point, and (3) an iteration takes O(n) time.  
*)
Module SimpleAnalysis.
  Import CPS.
  Import MonadNotation.
  Local Open Scope monad_scope.

  (** We will approximate values by a set of [absval_t]'s.  
     The constants are limited to those that appear in the
     program, and the declarations must be either a [Fn_d]
     or a [Prim_d], excluding [Proj_p]. *)
  Inductive absval_t := 
  | Con_av : constructor -> absval_t
  | Int_av : Z -> absval_t
  | Decl_av : decl -> absval_t.

  (** We'll use the name on the binder as the key for comparison *)
  Definition binder (d:decl) : var := 
    match d with 
      | Op_d x _ => x
      | Fn_d x _ _ => x
      | Prim_d x _ _ => x
      | Rec_d _ => "!bogus"%string
    end.

  (** Returns [true] if the two abstract values are equal. *)
  Definition eq_absval (a1 a2:absval_t) : bool := 
    match a1, a2 with 
      | Con_av c1, Con_av c2 => eq_dec c1 c2
      | Int_av i1, Int_av i2 => eq_dec i1 i2
      | Decl_av d1, Decl_av d2 => eq_dec (binder d1) (binder d2)
      | _, _ => false
    end.

  (** Simple set and environment operations *)
  Definition set_t := list.
  Definition empty_set {A} : set_t A := nil.
  Definition singleton_set {A} (x:A) : set_t A := (x::nil).
  Definition Val := set_t absval_t.
  Definition absenv_t := alist var Val.
  Fixpoint mem (a:absval_t) (V:Val) : bool := 
    match V with 
      | nil => false
      | a'::V' => eq_absval a a' || mem a V'
    end.
  Fixpoint insert (a:absval_t) (V:Val) : Val := 
    if mem a V then V else a::V.
  Definition union (V1 V2:Val) : Val := 
    List.fold_right insert V1 V2.
  Fixpoint subset (V1 V2:Val) : bool := 
    match V1 with 
      | nil => true
      | a::V1' => mem a V2 && subset V1' V2
    end.

  (** In our abstract interpretation, we will keep a global state
      that maps variables to a set of possible abstract values.  
      We will also record whether the analysis has changed the
      mapping of variables, indicating that we have not yet reached
      a fixed-point. *)
  Record st := { absenv : absenv_t ; changed : bool }.
  
  Definition M := state st.
  
  Definition get_var (x:var) : M Val := 
    s <- get; 
    match FMaps.lookup x (absenv s) with 
      | None => ret empty_set
      | Some v => ret v
    end.
  
  Definition put_var (x:var) (V:Val) : M unit := 
    s <- get ; 
    put {| absenv := FMaps.add x V (FMaps.remove x (absenv s)) ; 
           changed := changed s |}.
  
  Definition set_changed (b:bool) : M unit := 
    s <- get ; 
    put {| absenv := absenv s ; changed := b |}.
  
  Definition get_changed : M bool := 
    s <- get ; ret (changed s).
  
  (** Evaluate an operand to an abstract value *)
  Definition abseval_op (v:op) : M Val := 
    match v with 
      | Con_o c => ret (singleton_set (Con_av c))
      | Int_o i => ret (singleton_set (Int_av i))
      | Var_o x => get_var x
    end.

  (** Extract only those abstract values that are functions. *)  
  Definition only_functions (V : Val) : list ((list var) * exp)  := 
    List.fold_right 
    (fun x a => 
      match x with 
        | Decl_av (Fn_d f xs e) => (xs,e)::a
        | _ => a
      end) nil V.
  
  (** Extract only those abstract values that are tuples and 
      compute the nth projection off of that tuple. *)
  Fixpoint projV (n:nat) (V : Val) : M Val := 
    match V with 
      | nil => ret nil
      | (Decl_av (Prim_d x MkTuple vs))::rest => 
        a <- projV n rest ; 
        match nth_error vs n with 
          | None => ret a 
          | Some v => V <- abseval_op v ; ret (union V a)
        end
      | _::rest => projV n rest
    end.
  
  (** Add in all of the abstract values in [Vnew] to the set of values
      associated with variable [x], and set [changed] if the 
      set grows *)
  Definition add_binding (x:var) (Vnew : Val) : M unit := 
    Vold <- get_var x ; 
    let V := union Vold Vnew in 
      if subset V Vold then ret tt
        else 
          put_var x V ;; set_changed true.
  
  Fixpoint add_bindings (xs:list var) (VS : list Val) : M unit := 
    match xs, VS with 
      | x::xs, v::vs => add_binding x v ;; add_bindings xs vs 
      | _, _ => ret tt
    end.
  
  (** A conservative test that tells whether two abstract values
      may be equal.  We only rule out a few cases that are guaranteed
      to not be equal, and assume the rest may be equal. *)
  Fixpoint may_be_same (a1 a2:absval_t) : bool := 
    match a1, a2 with 
      | Con_av c1, Con_av c2 => eq_dec c1 c2
      | Int_av i1, Int_av i2 => eq_dec i1 i2
      | Con_av _, Decl_av (Fn_d _ _ _) => false
      | Con_av _, Decl_av (Prim_d _ MkTuple_p _) => false
      | Int_av _, Decl_av (Fn_d _ _ _) => false
      | Int_av _, Decl_av (Prim_d _ MkTuple_p _) => false
      | Decl_av (Fn_d _ _ _), Con_av _ => false
      | Decl_av (Fn_d _ _ _), Int_av _ => false
      | Decl_av (Prim_d _ MkTuple_p _), Con_av _ => false
      | Decl_av (Prim_d _ MkTuple_p _), Int_av _ => false
      | _, _ => true
    end.
  
  (** Returns true if the abstract value [a] may be in the set
      of abstract values [V]. *)
  Fixpoint may_contain (a:absval_t) (V:Val) : bool := 
    match V with 
      | nil => false
      | a'::V' => may_be_same a a' || may_contain a V'
    end.
  
  Definition pattern_to_absval (p:pattern) : absval_t := 
     match p with 
       | Con_p c => Con_av c 
       | Int_p i => Int_av i
     end.
  
  (** Run through the program and update the abstract bindings
      for each variable. *)
  Fixpoint abstep_exp (e:exp) : M unit := 
    match e with 
      | Halt_e v => ret tt
      | Let_e d e => abstep_decl d ;; abstep_exp e 
      | App_e v vs => 
        V <- abseval_op v ; 
        VS <- mapM abseval_op vs ; 
        iter (fun f => add_bindings (fst f) VS) (only_functions V) 
      | Switch_e v arms def => 
        V <- abseval_op v ; 
        iter (fun p => 
          if may_contain (pattern_to_absval (fst p)) V then 
            abstep_exp (snd p)
            else ret tt) arms ;;
        match def with 
          | None => ret tt
          | Some e => abstep_exp e
        end 
    end
  with abstep_decl (d:decl) : M unit := 
    match d with
      | Op_d x v => 
        V <- abseval_op v ; add_binding x V 
      | Prim_d x Proj_p ((Int_o i)::v::nil) => 
        Vtuple <- abseval_op v ; 
        V <- projV (Z.to_nat i) Vtuple ; 
        add_binding x V
      | Prim_d x p vs => add_binding x (singleton_set (Decl_av d)) 
      | Fn_d f xs e => 
        add_binding f (singleton_set (Decl_av d)) ;;
        abstep_exp e 
      | Rec_d ds => iter abstep_decl ds
    end.
  
  (* Iterate [abstep_exp] until we either run out of fuel or we
     reach a fixed-point (i.e., the sets of abstract values associated
     with each variable have settled.)  Returns [true] if we 
     reach a fixedpoint, [false] if we run out of fuel. *)
  Fixpoint findfixpoint (n:nat) (e:exp) : M bool := 
    match n with 
      | 0 => ret false
      | S n => 
        set_changed false ;; abstep_exp e ;; 
        b <- get_changed ; if b then findfixpoint n e else ret true
    end.
  
  Definition initial_absenv : absenv_t := nil.
  
  Definition initial_st : st := {| absenv:=initial_absenv ; changed := false|}.
  
  Definition absinv (n:nat) (e:exp) : option absenv_t := 
    let p := runState (findfixpoint n e) initial_st in
      if (fst p) then Some (absenv (snd p)) else None.

  (** Tools for printing out the mapping of variables to sets of
      abstract values. *)
  Definition emit_absval (a:absval_t) : state (list string) unit := 
    emit "  ";;
    match a with 
      | Con_av c => emit ("Con(" ++ c ++ ")")
      | Int_av i => emit (z2string i)
      | Decl_av d => emitdecl false 2 d
    end ;; 
    emit newline.

  Fixpoint emit_env (env:absenv_t) : state (list string) unit := 
    match env with 
      | nil => emit newline
      | (x,V)::rest => 
        emit (x ++ " = [" ++ newline) ;; 
        iter emit_absval V ;; 
        emit ("]" ++ newline) ;; 
        emit_env rest
    end.

  Definition absenv2string (envopt:option absenv_t) : string := 
    match envopt with 
      | None => "<fail>"
      | Some env => 
        newline ++ 
        (List.fold_left (fun x y => y ++ x)
          (snd (runState (emit_env env) nil)) "")
  end%string.

(*
  Module Test.
    Require Import Lambda.
    Import LambdaNotation.
    Require Import Optimize.
    
    Definition e0 := 
      def f := \a => a in
      def x := f @ Z_c in
      def y := f @ (S_c Z_c) in
      [[ x, y ]].

    Definition c0 := Optimize.optimize 100 (CPS (gen e0)).
    Eval compute in exp2string c0.
    Eval compute in absenv2string (absinv 100 c0).

    Definition e1 := 
      defrec dec[n] := 
        nat_match n with 
          Z => Z_c
        | S[m] => dec @ m
      in 
        dec @ two.

    Definition c1 := (Optimize.optimize 100 (CPS (gen e1))).
    Eval compute in exp2string c1.
    Eval compute in absenv2string (absinv 100 c1).
  End Test.
*)
End SimpleAnalysis.
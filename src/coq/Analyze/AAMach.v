Require Import CoqCompile.Cps.
(* must import ZArith first, otherwise coq wont recognize Z type *)
Require Import ZArith List String Bool.
Require Import ExtLib.Sets.ListSet.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

(* implements Abstracting Abstract Machines from class 2012-10-22 *)

Module AAMach.
  Import CPS.

  (********** type definitions **********)

  (* abstract values *)
  Inductive hval : Type := 
  | Con_h : constructor -> hval
  | Z_h : Z -> hval
  | Tup_h : list var -> hval
  (* | Clo_h : env_t (lset (@eq hval)) -> list var -> exp -> hval. *)
  (* dont need closures? *)
  | Lam_h : list var -> exp -> hval.

  Definition is_Z_h (v:hval) :bool:=
    match v with
      | Z_h _ => true
      | _ => false
    end.
  Definition is_Tup_h (v:hval): bool:=
    match v with 
      | Tup_h _ => true
      | _ => false
    end.
  Definition is_Lam_h (v:hval):bool:=
    match v with
      | Lam_h _ _ => true
      | _ => false
    end.
  Definition is_Con_h (v:hval):bool:=
    match v with
      | Con_h _ => true
      | _ => false
    end.


  (* sets of abstract values *)
  Definition hset := lset (@eq hval).

  (* abstract environment mapping variables to sets of abstract values *)  
  Definition henv := env_t hset.


(********** equality functions **********)

  Definition exp_eq_dec : forall (x y:exp), {x=y}+{x<>y}.
    fix exp_eq_dec 1
      with (decl_eq_dec (x y:decl) {struct x}: {x=y}+{x<>y}).
    repeat decide equality.
    repeat decide equality.
  Defined.

  Definition exp_eq_bool (e1 e2: exp) : bool :=
    if exp_eq_dec e1 e2 then true else false.

  Definition string_dec_bool (s1 s2: string) : bool :=
    if string_dec s1 s2 then true else false.

Section eq_list.
  Context {A:Type}.
  Variable (eqA:A->A->bool).
  Fixpoint eq_list (l1 l2: list (A)): bool:=
    match l1,l2 with
      | nil,nil => true
      | (a1)::q1,(a2)::q2=> eqA a1 a2 && eq_list q1 q2
      | _,_ => false
    end.
End eq_list.

(* Section eq_pair. *)
(*   Context {A B :Type}. *)
(*   Variable (eqA:A->A->bool). *)
(*   Variable (eqB:B->B->bool). *)
(*   Fixpoint eq_pair (p1 p2: A*B): bool := *)
(*     match p1,p2 with *)
(*       | (p1a,p1b),(p2a,p2b) => eqA p1a p2a && eqB p1b p2b *)
(*     end. *)
(* End eq_pair. *)

(* Section eq_env. *)
(*   Context {A:Type}. *)
(*   Variable (eqA:A->A->bool). *)
(*   Definition eq_env (env1 env2: env_t A):bool:= *)
(*     eq_list (eq_pair string_dec_bool eqA) env1 env2. *)
(* End eq_env. *)

(* Section eq_set. *)
(*   Context{A:Type}. *)
(*   Variable(eqA:A->A->bool). *)
(*   Definition eq_set (set1 set2: lset (@eq A)):bool:= *)
(*     eq_list eqA set1 set2. *)
(* End eq_set. *)

  Fixpoint hval_eq (h1 h2: hval) : bool :=
    match h1, h2 with
      | Con_h c1, Con_h c2 => string_dec_bool c1 c2
      | Z_h z1, Z_h z2 => Zeq_bool z1 z2
      | Tup_h xs1, Tup_h xs2 => eq_list string_dec_bool xs1 xs2
      (* | Clo_h env1 xs1 e1, Clo_h env2 xs2 e2 =>  *)
      (*   eq_env (eq_set hval_eq) env1 env2 && *)
      (*   eq_list string_dec_bool xs1 xs2 && *)
      (*   exp_eq_bool e1 e2 *)
      | Lam_h xs1 e1, Lam_h xs2 e2 =>
        eq_list string_dec_bool xs1 xs2 && exp_eq_bool e1 e2
      | _,_  => false
    end.
  Definition hval_eq_prop (h1 h2:hval):Prop:=
    if hval_eq h1 h2 then True else False.
 



(********** set functions **********)

(* returns union of vs1 and vs2 *)
Fixpoint hset_union (vs1:hset) (vs2:hset):hset:=
  match vs1 with
    | nil => vs2
    | v::vs => hset_union vs (lset_add hval_eq v vs2)
  end.

(* filters out elements x of vs where f(x) = false *)
Fixpoint hset_filter (f:hval->bool) (vs:hset) : hset :=
  match vs with
    | nil => nil
    | v::rest => if f v then v::hset_filter f rest else hset_filter f rest
  end. 



(********** env functions **********)

(* extend env(x) with v, ie env(x) = env(x) \cup {v} *)
Fixpoint extend_env (env:henv) (x:var) (v:hval): henv:=
  match env with
    | nil => (x,(lset_add hval_eq v (lset_empty hval_eq_prop)))::nil
    | (y,vs)::rest => 
      if string_dec x y 
        then (x,(lset_add hval_eq v vs))::rest
        else (y,vs)::extend_env rest x v
  end.

(* extend env(x) with vs, ie env(x) = env(x) \cup vs *)
Fixpoint extend_envs (env:henv) (x:var) (vs:hset):henv:=
  match env with
    | nil => (x,vs)::nil
    | (y,vs2)::rest =>
      if string_dec x y
        then (x,hset_union vs vs2)::rest
        else (y,vs2)::extend_envs rest x vs
  end.

Local Open Scope string_scope.

Definition h1 := Con_h "A".
Definition h2 := Con_h "B".
Definition h3 := Tup_h ("x"::"y"::"z"::nil).
Definition h4 := Tup_h ("a"::"b"::nil).
Definition h5 := Z_h 2.

Definition env1 := extend_env nil "x" h1.
Definition env2 := extend_env env1 "x" h2.
Definition env3 := extend_env env2 "x" h1.
(* h1 ("A") should only appear once *)
Eval compute in env3.
Definition env4 := extend_env env3 "y" h1.
Definition env5 := extend_env env4 "y" h3.
Eval compute in env5.

(* extracts var from Op *)
Definition o2x (o:op):var :=
  match o with
    | Var_o x => x
    | _ => "x" (* shouldnt get here bc we are assuming only vars *)
  end.

Local Close Scope string_scope.

(* non-option version of env lookup, return emptyset if x\notin dom(env)*)
Fixpoint env_lookup (env:henv) (x:var):hset:=
  match env with
    | nil => (lset_empty hval_eq_prop)
    | (y,vs)::rest => if string_dec x y then vs else env_lookup rest x
  end.

(* env(x) = env(x) \cup env(\pi i tup) *)
Fixpoint extend_env_proj_tup (env:henv) (x:var) (i:Z) (tup:list var): henv:=
  extend_envs env x (env_lookup env (nth (Z.abs_nat i) tup x)).

(* extend env(x) with ith element of every tuple in tups *)
Fixpoint extend_env_proj (env:henv) (x:var) (i:Z) (tups:hset):henv:=
  match tups with 
    | nil => env
    | (Tup_h xs)::rest => 
      extend_env_proj (extend_env_proj_tup env x i xs) x i rest
    | _ => env (* can get here bc tups is all Tup_h *)
  end.

(* for x in xs, extend env(x) with env(arg), for corresponding arg in args *)
Fixpoint extend_env_xs (env:henv) (xs:list var) (args:list var):henv:=
  match xs,args with
    | nil,nil => env
    | x::rest,y::restargs => 
      extend_env_xs (extend_envs env x (env_lookup env y)) rest restargs
    | _,_ => env
  end.
      
(* merge two environments, extending when appropriate, and adding otherwise *)
Fixpoint merge_envs (env1:henv) (env2:henv):henv:=
  match env1,env2 with 
    | nil,nil => nil
    | nil,_ => env2
    | _,nil => env1
    | (x,vs)::rest,_ => merge_envs rest (extend_envs env2 x vs)
  end.



Local Open Scope string_scope.

(********** Abstracting Abstract Machines **********)

(* extend env with decl d *)
Fixpoint extend (env:henv) (d:decl) : henv :=
  match d with
    | Op_d x (Con_o c) => extend_env env x (Con_h c)
    | Op_d x (Int_o z) => extend_env env x (Z_h z)
    | Prim_d x Plus_p xs => extend_env env x (Con_h "Int")
    | Prim_d x MkTuple_p os => extend_env env x (Tup_h (map o2x os))
    | Prim_d x Proj_p ((Int_o i)::tup::nil) => 
      extend_env_proj env x i (hset_filter is_Tup_h (env_lookup env (o2x tup)))
    | Fn_d f xs e => extend_env env f (Lam_h xs e)
    | Rec_d ds =>
      (fix map_extend (ds:list decl) (env:henv): henv :=
        match ds with
          | nil => env
          | d::rest => map_extend rest (extend env d)
        end) ds env
    | _ => env
  end.

Local Close Scope string_scope.

(* given machine state of e and env, compute list of envs, 
   one for each possible final state *)
Fixpoint aeval (fuel:nat) (e:exp) (env:henv) : list henv:=
  match fuel with
    | 0 => nil
    | S n => 
      match e with
        | App_e o os => 
          let lams := hset_filter is_Lam_h (env_lookup env (o2x o)) in
          let args := map o2x os in
            flat_map
            (fun v => 
              match v with
                | Lam_h xs e => aeval n e (extend_env_xs env xs args)
                | _ => nil
              end)
            lams
        | Let_e d e => aeval n e (extend env d)
        | Switch_e o arms def => 
          (flat_map
            (fun arm => 
              match arm with 
                | (_,e) => aeval n e env
              end)
            arms) ++
          (match def with
             | None => nil
             | Some e => aeval n e env
           end)
        | Halt_e o => env::nil
      end
  end.

(* computes abstract env for given program e 
   by merging all envs from possible states *)
Definition inj (e:exp) : henv := fold_left merge_envs (aeval 100 e nil) nil.



Local Open Scope string_scope.

Definition e1 := Halt_e (Var_o "x").
Eval compute in inj e1.

Definition e2 := Let_e (Op_d "x" (Var_o "y")) e1.
Eval compute in inj e2.

(* test projection *)
Definition e3 := Let_e (Op_d "x" (Con_o "A"))
                  (Let_e (Op_d "y" (Con_o "B"))
                   (Let_e (Prim_d "z" MkTuple_p (Var_o "x"::Var_o "y"::nil))
                     (Let_e (Op_d "w" (Con_o "C"))
                       (Let_e (Prim_d "w" Proj_p (Int_o 0::Var_o "z"::nil))
                         (Halt_e (Var_o "w")))))).
(* env(w) should be "C" and either "A" or "B", 
   depending on whether e3 gets the 1st or 2nd element from tuple "z" *)
Eval compute in inj e3.

Definition e4 :=
  Let_e (Op_d "1" (Int_o 1))
   (Let_e (Op_d "2" (Int_o 2))
     (Let_e (Op_d "3" (Int_o 3))
       (Let_e (Op_d "4" (Int_o 4))
         (Let_e (Fn_d "f" ("x"::"y"::nil)
                  (Let_e (Prim_d "z" Plus_p (Var_o "x"::Var_o "y"::nil))
                    (Halt_e (Var_o "z"))))
           (App_e (Var_o "f") (Var_o "1"::Var_o "2"::nil)))))).
(* result "z" should have abstract value "Int" *)
Eval compute in inj e4.

(* test combining of fn parameters of the same name*)
Definition e5 :=
  Let_e (Op_d "1" (Int_o 1))
   (Let_e (Op_d "2" (Int_o 2))
     (Let_e (Op_d "3" (Int_o 3))
       (Let_e (Op_d "4" (Int_o 4))
         (Let_e (Fn_d "g" ("x"::"y"::nil)
                  (Let_e (Prim_d "z" Plus_p (Var_o "x"::Var_o "y"::nil))
                    (Halt_e (Var_o "z"))))
           (Let_e (Fn_d "f" ("x"::"y"::nil)
                    (App_e (Var_o "g") (Var_o "3"::Var_o "4"::nil)))
             (App_e (Var_o "f") (Var_o "1"::Var_o "2"::nil))))))).
(* env(x) and env(y) should have multiple values: 1 and 3, and 2 and 4 *)
Eval compute in inj e5.

(* test multiple possible tuples in a projection *)
Definition e6 :=
  Let_e (Op_d "1" (Int_o 1))
   (Let_e (Op_d "2" (Int_o 2))
     (Let_e (Op_d "3" (Int_o 3))
       (Let_e (Op_d "4" (Int_o 4))
         (Let_e (Prim_d "tup1" MkTuple_p (Var_o "1"::Var_o "2"::nil))
           (Let_e (Prim_d "tup2" MkTuple_p (Var_o "3"::Var_o "4"::nil))
             (Let_e (Fn_d "g" ("x"::nil)
                      (Let_e (Prim_d "z" Proj_p (Int_o 1::Var_o "x"::nil))
                        (Halt_e (Var_o "z"))))
               (Let_e (Fn_d "f" ("x"::nil)
                        (App_e (Var_o "g") (Var_o "tup2"::nil)))
                 (App_e (Var_o "f") (Var_o "tup1"::nil))))))))).
(* env(x) should have both tuples,
    and "z" should have two values, one from each tuple *)
Eval compute in inj e6.

(* test multiple possible lambdas in app *)
Definition e7 :=
  Let_e (Op_d "1" (Int_o 1))
   (Let_e (Op_d "2" (Int_o 2))
     (Let_e (Op_d "3" (Int_o 3))
       (Let_e (Op_d "4" (Int_o 4))
         (Let_e (Fn_d "g1" ("x1"::"y1"::nil)
                  (Let_e (Prim_d "z1" Plus_p (Var_o "x1"::Var_o "y1"::nil))
                    (Halt_e (Var_o "z1"))))
           (Let_e (Fn_d "g2" ("x2"::"y2"::nil)
                    (Let_e (Prim_d "z2" Plus_p (Var_o "x2"::Var_o "y2"::nil))
                      (Halt_e (Var_o "z2"))))
             (Let_e (Fn_d "g3" ("x3"::"y3"::nil)
                      (Let_e (Prim_d "z3" Plus_p (Var_o "x3"::Var_o "y3"::nil))
                        (Halt_e (Var_o "z3"))))
               (Let_e (Fn_d "f" ("g"::"x"::"y"::nil)
                        (App_e (Var_o "g") (Var_o "x"::Var_o "y"::nil)))
                 (Switch_e (Var_o "1")
                   ((Int_p 1,(App_e (Var_o "f") (Var_o "g1"::Var_o "1"::Var_o "2"::nil)))::
                    (Int_p 2,(App_e (Var_o "f") (Var_o "g2"::Var_o "3"::Var_o "4"::nil)))::nil)
                   (Some (App_e (Var_o "f") (Var_o "g3"::Var_o "2"::Var_o "3"::nil))))))))))).
(* g should be bound to three lambdas, 
   all of x1-3, y1-3, z1-3 should be bound,
   and x and y should be bound to three values each *)
Eval compute in inj e7.




Close Scope string_scope.

End AAMach.
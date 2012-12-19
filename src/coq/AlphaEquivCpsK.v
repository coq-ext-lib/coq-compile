Require Import List.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Monads.ReaderMonad ExtLib.Data.Monads.OptionMonad.

Set Implicit Arguments.
Set Strict Implicit.

Module Alpha.
  Import CPSK.

  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : DMap var env_v}.
    Variable env_k : Type -> Type.
    Context {Mk : DMap cont env_k}.
    
    Section monadic. 
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {Reader_var : MonadReader (env_v var) m}.
      Context {Reader_cont : MonadReader (env_k cont) m}.
      Context {Zero_m : MonadZero m}.

      Import MonadNotation.
      Local Open Scope monad_scope.
      Local Open Scope list_scope. 
  
      Definition alpha_op (o1 o2 : op) : m unit :=
        match o1 , o2 with
          | Var_o v1 , Var_o v2 =>
            x <- ask ;;
            match Maps.lookup v1 x with
              | None => assert (eq_dec v1 v2)
              | Some v1 => assert (eq_dec v1 v2)
            end
          | Con_o c1 , Con_o c2 =>
            assert (eq_dec c1 c2)
          | Int_o z1 , Int_o z2 =>
            assert (eq_dec z1 z2)
          | _ , _ => assert false
        end.

      Definition alpha_k (k1 k2 : cont) : m unit :=
        k2' <- asks (Maps.lookup k1) ;;
        match k2' with
          | None => assert (eq_dec k1 k2)
          | Some k2' => assert (eq_dec k2' k2)
        end.

      Fixpoint all2 {T} (p : T -> T -> m unit) (ls1 ls2 : list T) : m unit :=
        match ls1 , ls2 with
          | nil , nil => ret tt
          | l1 :: ls1 , l2 :: ls2 =>
            p l1 l2 ;;
            all2 p ls1 ls2
          | _ , _ => assert false
        end.

      Global Instance RelDec_eq_pattern : RelDec (@eq pattern) :=
      { rel_dec := fun x y =>
        match x , y with
          | Int_p x , Int_p y => eq_dec x y
          | Con_p x , Con_p y => eq_dec x y
          | _ , _ => false
        end }.

      Fixpoint alpha_exp' (e1 e2 : exp) {struct e1} : m unit :=
        match e1, e2 with
          | App_e f1 ks1 args1 , App_e f2 ks2 args2 =>
            alpha_op f1 f2 ;;
            all2 alpha_k ks1 ks2 ;;
            all2 alpha_op args1 args2
          | Let_e d1 e1 , Let_e d2 e2 =>
            alpha_dec d1 d2 (alpha_exp' e1 e2)

          | Letrec_e ds1 e1 , Let_e ds2 e2 =>
            assert false 
(*
            alpha_dec ds1 ds2 (alpha_exp' e1 e2)
*)

          | Switch_e op1 br1 e1 , Switch_e op2 br2 e2 =>
            alpha_op op1 op2 ;;
            match e1 , e2 with
              | None , None => assert true
              | Some e1 , Some e2 =>
                alpha_exp' e1 e2
              | _ , _ => assert false
            end ;;
            (fix all2 ls1 ls2 : m unit :=
              match ls1 , ls2 with
                | nil , nil => assert true
                | (p1,e1) :: ls1 , (p2,e2) :: ls2 =>
                  assert (eq_dec p1 p2) ;;
                  alpha_exp' e1 e2 ;;
                  all2 ls1 ls2
                | _ , _ => assert false
              end) br1 br2             
          | Halt_e o1 o1', Halt_e o2 o2'=>
            alpha_op o1 o2 ;;
            alpha_op o1' o2'
          | AppK_e k1 o1 , AppK_e k2 o2 =>
            alpha_k k1 k2 ;;
            all2 alpha_op o1 o2 
          | LetK_e k1 e1 , LetK_e k2 e2 =>
            assert false (** TODO **)
          | _ , _ => assert false
        end
      with alpha_dec (d1 d2 : decl) (k : m unit) {struct d1} : m unit :=
        match d1 , d2 with
          | Op_d v1 o1 , Op_d v2 o2 =>
            alpha_op o1 o2 ;;
            local (add v1 v2) k
          | Prim_d v1 p1 args1 , Prim_d v2 p2 args2 =>
            assert (eq_dec p1 p2) ;;
            all2 alpha_op args1 args2 ;;
            local (add v1 v2) k
          | Bind_d v1 w1 p1 args1 , Bind_d v2 w2 p2 args2 =>
            assert (eq_dec p1 p2) ;;
            all2 alpha_op args1 args2 ;;
            local (fun x => add v1 v2 (add w1 w2 x)) k
          | Fn_d v1 k1 a1 e1 , Fn_d v2 k2 a2 e2 =>
            (fix map_multi (x y : list var) (k : m unit) : m unit :=
              match x , y with
                | nil , nil => 
                  (fix map_multi (x y : list cont) (k : m unit) : m unit :=
                    match x , y with
                      | nil , nil => k
                      | x :: xs , y :: ys =>
                        local (add x y) (map_multi xs ys k)
                      | _ , _ => assert false
                    end
                  ) k1 k2 k
                | x :: xs , y :: ys => 
                  local (add x y) (map_multi xs ys k)
                | _ , _ => assert false
              end) a1 a2 (alpha_exp' e1 e2) ;;
            local (add v1 v2) k 
          | _ , _ => assert false
        end.
    End monadic.
  End maps.

  Definition alpha_exp (e1 e2 : exp) : bool :=
    let res := runReader (runReaderT (unOptionT (alpha_exp' (m := optionT (readerT (alist var var) (reader (alist cont cont)))) e1 e2)) empty) empty in
    match res with
      | None => false
      | Some _ => true
    end.

  Definition alpha_lam (e1 e2 : exp) (v1 v2 : list var) (k1 k2 : list cont) : bool :=
    (fix build acc l1 l2 {struct l1} : bool :=
      match l1 , l2 with
        | nil , nil => 
          let res := runReader (runReaderT (unOptionT (alpha_exp' (m := optionT (readerT (alist var var) (reader (alist cont cont)))) e1 e2)) acc) empty (** TODO **) in
          match res with
            | None => false
            | Some _ => true
          end
        | l1 :: ls1 , l2 :: ls2 =>
          build (add l1 l2 acc) ls1 ls2
        | _ , _ => false
      end) empty v1 v2.
  
  Module TEST.
    Require Import String.

    Require Import BinNums.
    (** Test cases needed **)
    Definition f (n : Z) (v : var) : exp := 
      Let_e (Prim_d v Proj_p (Int_o n :: nil))
      (Halt_e (Var_o v) (Var_o (wrapVar "world"%string))).

    Goal (alpha_exp (f 2 (wrapVar "0")) (f 1 (wrapVar "2")) = false)%string.
    Proof. vm_compute; reflexivity. Abort.

    Goal (alpha_exp (f 2 (wrapVar "0")) (f 2 (wrapVar "0")) = true)%string.
    Proof. vm_compute; reflexivity. Abort.
(*
    Goal (alpha_lam (f (wrapVar "0")) (f (wrapVar "1")) (wrapVar "0" :: nil) (wrapVar "1" :: nil) = true)%string.
    Proof. vm_compute; reflexivity. Abort.

    Goal (alpha_lam (f (wrapVar "0")) (f (wrapVar "1")) (wrapVar "0" :: nil) (wrapVar "2" :: nil) = false)%string.
    Proof. vm_compute; reflexivity. Abort.
*)
  End TEST.

End Alpha.
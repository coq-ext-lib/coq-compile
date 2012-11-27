Require Import String List BinPos.
Require Import CoqCompile.CpsK CoqCompile.CpsKUtil.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Programming.Show.

Set Implicit Arguments.
Set Strict Implicit.

Module ClosureConvert.
  Import CPSK.

  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : DMap var env_v}.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {State_m : MonadState positive m}.
    Context {Writer_m : MonadWriter (@Monoid_list_app decl) m}.
    Context {Reader_m : MonadReader (env_v op) m}.
    Context {Exc_m : MonadExc string m}.
    (** I need some way to encapsulate when calls should use a specified environment
     **)

    Import MonadNotation.
    Local Open Scope monad_scope.

    Definition fresh (s : string) : m var :=
      n <- modify Psucc ;;
      ret (mkVar (Some s) n).

    Definition freshFor (v : var) : m var :=
      n <- modify Psucc ;;
      match v with 
        | Anon_v _ => ret (Anon_v n)
        | Named_v s p => 
          ret (Named_v s (Some n))
      end.

    Definition cloconv_op (o : op) : m op :=
      match o with
        | Var_o v =>
          x <- ask (MonadReader := Reader_m) ;;
          match Maps.lookup v x with
            | None => ret o
            | Some v => ret v
          end          
        | Con_o _ => ret o
        | Int_o _ => ret o
        | InitWorld_o => ret o
      end.

    Definition cloconv_k (k : cont) : m cont := ret k.

    Definition liftDecl (d : decl) : m unit :=
      tell (d :: nil).

    Fixpoint underBinders (o : op) (ls : list var) (from : nat) (c : m exp) {struct ls} : m exp :=
      match ls with 
        | nil => c
        | l :: ls => 
          l' <- freshFor l ;;
          e <- local (Maps.add l (Var_o l')) (underBinders o ls (S from) c) ;;
          ret (Let_e (Prim_d l' Proj_p (Int_o (PreOmega.Z_of_nat' from) :: o :: nil)) e)
      end.

    Definition withVars {T} (ls : list (var * op)) : m T -> m T :=
      local (fold_left (fun mp vo => Maps.add (fst vo) (snd vo) mp) ls).

    Fixpoint usingEnvForAll (env : op) (ls : list (var * var)) (c : m exp) : m exp :=
      match ls with
        | nil => c
        | (name, code_name) :: ls => 
          z <- freshFor name ;;
          local (Maps.add name (Var_o z))
            (e <- usingEnvForAll env ls c ;;
             ret (Let_e (Prim_d z MkTuple_p (Var_o code_name :: env :: nil)) e))
      end.

    Fixpoint alist_lookup {K V} (R : RelDec (@eq K)) (k : K) (ls : list (K * V)) : option V :=
      match ls with
        | nil => None
        | l :: ls => if eq_dec k (fst l) then Some (snd l) else alist_lookup _ k ls
      end.

    Fixpoint cloconv_exp' (e : exp) : m exp.
    refine (
      match e with
        | AppK_e k args =>
          args <- mapM cloconv_op args ;;
          k <- cloconv_k k ;;
          ret (AppK_e k args)
        | LetK_e ks e =>
          ks <- mapM (fun k_xs_e => let '(k,xs,e) := k_xs_e in
                        e <- cloconv_exp' e ;;
                        ret (k, xs, e)) ks ;;
          e <- cloconv_exp' e ;;
          ret (LetK_e ks e)
        | App_e f ks args =>
          f <- cloconv_op f ;;
          args <- mapM cloconv_op args ;;
          f_code <- fresh "cptr" ;;
          ret (Let_e (Prim_d f_code Proj_p (Int_o 0 :: f :: nil))
                     (App_e (Var_o f_code) ks (f :: args)))
        | Switch_e o arms def =>
          o <- cloconv_op o ;;
          arms <- mapM (fun pe =>
            let '(p,e) := pe in
            e <- cloconv_exp' e ;;
            ret (p, e)) arms ;;
          def <- match def with
                   | None => ret None
                   | Some def => def <- cloconv_exp' def ;; ret (Some def)
                 end ;;
          ret (Switch_e o arms def)
        | Halt_e o1 o2 =>
          o1 <- cloconv_op o1 ;;
          o2 <- cloconv_op o2 ;;
          ret (Halt_e o1 o2)
        | Let_e (Op_d v o) e =>
          o <- cloconv_op o ;;
          e <- cloconv_exp' e ;;
          ret (Let_e (Op_d v o) e)
        | Let_e (Prim_d v p os) e =>
          os <- mapM cloconv_op os ;;
          e <- cloconv_exp' e ;;
          ret (Let_e (Prim_d v p os) e) 
        | Let_e (Bind_d x w m os) e =>
          os <- mapM cloconv_op os ;;
          e <- cloconv_exp' e ;;
          ret (Let_e (Bind_d x w m os) e) 
        | Let_e (Fn_d v ks vs e') e =>
          let fvars := free_vars_decl false (Fn_d v ks vs e') in
          fvars <- mapM (fun v' =>
            match v' with
              | inl v => ret v
              | inr x => raise ("Invariant violation: escaping continuation " ++ runShow (show x) ++ " from " ++ runShow (show v))%string
            end) fvars ;;
          (** fvars does not contain duplicates **)
          envV <- fresh "env"%string ;;
          v_code <- freshFor v ;;
          e' <- underBinders (Var_o envV) fvars 1 (cloconv_exp' e') ;;
          e <- cloconv_exp' e ;;
          liftDecl (Fn_d v_code ks (envV :: vs) e') ;;
          fvars' <- mapM (T := lset eq) cloconv_op (map Var_o fvars) ;;
          ret (Let_e (Prim_d v MkTuple_p (Var_o v_code :: fvars'))
                     e)
        | Letrec_e ds e_body => _
      end).
    refine (
          let func_names := fold_left (fun acc d =>
            match d with
              | Fn_d v _ _ _ => v :: acc
              | _ => acc
            end) ds nil in
          (** Find all the functions and get the combined environment **)
          let env : list (var + cont) := toList (monoid_sum (@Monoid_set_union _ _ _ _)
            (map (fun d => 
              match d with 
                | Fn_d _ _ _ _ => free_vars_decl true d
                | _ => monoid_unit (@Monoid_set_union _ _ _ _)
              end) ds))
          in
          (** Remove the recursive functions from the environment **)
          let env := filter (fun x => 
            match x with
              | inl x => negb (anyb (eq_dec x) func_names)
              | inr x => false
            end) env in
          env <- mapM (fun x => match x with
                                  | inl x => ret x
                                  | inr x =>
                                    raise "ERROR: found continuation in list"%string
                                end) env ;;
          let _ : list var := env in
          (** The names for the code **)
          funcCodeNames <- mapM (fun n => 
            v <- freshFor n ;; 
            vw <- freshFor n ;; 
            ret (n, (v, vw))) func_names ;;
          let funcCodeOps := map (fun x => let '(a,(b,_)) := x in (a, b)) funcCodeNames in

          (** Lift the functions & wrappers out **)
          iterM (fun d =>
            match d with
              | Fn_d v ks vs e =>
                envV <- fresh "env" ;;
                e <- usingEnvForAll (Var_o envV) funcCodeOps (underBinders (Var_o envV) env 0 (cloconv_exp' e)) ;;
                match alist_lookup _ v funcCodeNames with
                  | None => ret tt (** Dead Code **)
                  | Some (cptr, cptr_wrap) =>
                    liftDecl (Fn_d cptr ks (envV :: vs) e) ;;
                    zV <- fresh "env" ;;
                    liftDecl (Fn_d cptr_wrap ks (envV :: vs) 
                                   (Let_e (Prim_d zV Proj_p (Int_o (PreOmega.Z_of_nat' 1) :: Var_o envV :: nil))
                                          (App_e (Var_o cptr) ks (Var_o zV :: map Var_o vs))))
                end
              | _ => ret tt
            end) ds ;;

          all_envV <- fresh "env" ;;
          let all_env_d := Prim_d all_envV MkTuple_p (map Var_o env) in
          let _ : list decl := ds in
          (** Construct non-functions & wrapper closures **)
          ds' <- mapM (fun d =>
            match d with
              | Fn_d v _ _ _ =>
                match alist_lookup _ v funcCodeNames with
                  | None => ret d (** Dead Code **)
                  | Some (_, cptr_wrap) =>
                    ret (Prim_d v MkTuple_p (Var_o cptr_wrap :: Var_o all_envV :: nil))
                end 
              | Prim_d v p os =>
                os <- mapM cloconv_op os ;;
                ret (Prim_d v p os)
              | Bind_d x w m os =>
                os <- mapM cloconv_op os ;;
                ret (Bind_d x w m os)
              | Op_d v o =>
                o <- cloconv_op o ;;
                ret (Op_d v o)
            end) ds ;;
          let _ : list decl := ds' in
          (** Cps the result **)
          let var_map : list (var * op) := 
            fold_left (fun acc d => 
              match d with
                | Fn_d v _ _ _ => (v, Var_o v) :: acc
                | Prim_d v _ _ => (v, Var_o v) :: acc
                | Bind_d x w _ _ => (x, Var_o x) :: (w, Var_o w) :: acc
                | Op_d v _ => (v, Var_o v) :: acc
              end) ds nil
          in
          e <- withVars var_map (cloconv_exp' e_body) ;;
          (** Return everything **)
          ret (Letrec_e (all_env_d :: ds') e)).
    Defined.
    
  End monadic.
  
  End maps.

  Require Import ExtLib.Data.Map.FMapAList.
  Require Import ExtLib.Data.Monads.WriterMonad.
  Require Import ExtLib.Data.Monads.ReaderMonad.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Monads.EitherMonad.

  Import MonadNotation.
  Local Open Scope monad_scope.
  
  Definition cloconv_exp (e : exp) : string + (list decl * exp) :=
    let env_v := alist var in
    let c := cloconv_exp' (env_v := env_v)
      (m := readerT (env_v op) (readerT (env_v (var * var)%type) (writerT (@Monoid_list_app decl) (stateT positive (sum string))))) 
      e in
    res <- runStateT (runWriterT (runReaderT (runReaderT c Sets.empty) Maps.empty)) 1%positive ;;
    let '(e', ds', _) := res in
    ret (ds', e').


(*
  Module Tests.

    Require Import Lambda.
    Import LambdaNotation.
    Require Import ExtLib.FMaps.FMapAList.
    Require Import Arith.

   (* This tries to check that two heap values / values really are
      "equivalent" - only works for tuples of values. We return false
      if we try to compare closures. "depth" parameter is fuel for how deep to check 
      the equivalence. Maybe break this out into a separate testing thing,
      since this would work for testing optimizations on CPS form as well *)

    Fixpoint compare_heap_value (depth: nat) (heap1 heap2: heap) (hv1 hv2: heap_value) :=
      match depth with
        | O => true
        | S d' => 
          match hv1, hv2 with
            | Tuple_v lv1, Tuple_v lv2 =>  
              if eq_nat_dec (List.length lv1) (List.length lv2) then
                List.fold_left 
                  (fun acc vs => andb acc (compare_value d' heap1 heap2 (fst vs) (snd vs))) 
                  (List.combine lv1 lv2) true 
                else
                  false
            | _, _ => false
          end
      end
    with
      compare_value (depth: nat) h1 h2 v1 v2 :=
      match depth with
        | O => true
        | S d' =>
          match v1, v2 with
            | Con_v c1, Con_v c2 => eq_dec c1 c2 
            | Int_v z1, Int_v z2 => eq_dec z1 z2
            | Ptr_v n1, Ptr_v n2 => 
              match (run (heap_lookup n1) h1), (run (heap_lookup n2) h2) with
                | (Some hv1, _), (Some hv2, _) => compare_heap_value d'  h1 h2 hv1 hv2 
                | _, _ => false
              end
            | _, _ => false
          end
      end.

    (* Just a wrapper to make this easier to use *)
    Definition compare dfuel rfuel e1 e2 :=
      match (eval rfuel e1), (eval rfuel e2) with
        | (Some hv1, h1), (Some hv2, h2) => 
          compare_heap_value dfuel h1 h2 (Tuple_v hv1) (Tuple_v hv2)
        | _, _ => false
      end.

    Definition cc1 := CPS (gen (def y := S_c Z_c in def z := S_c Z_c in S_c y)).
    Eval compute in (exp2string cc1).
    Eval compute in (exp2string (cloconv_exp cc1)).
    Eval compute in (compare 200 200 cc1 (cloconv_exp cc1)).

    Definition cc2 := CPS (gen e2).
    
    Eval compute in (exp2string cc2).
    Eval compute in (exp2string (cloconv_exp cc2)).
    (* This returns a closure, so can't use compare to check *)

    Definition cc3 := CPS (gen e4).
    Eval compute in (exp2string cc3).
    Eval compute in (exp2string (cloconv_exp cc3)).
    (* This diverges, so can't check *)

    Definition cc4 := CPS (gen e5).
    Eval compute in exp2string cc4.
    Eval compute in exp2string (cloconv_exp cc4).
    Eval compute in (compare 200 200 cc4 (cloconv_exp cc4)).

    Definition cc5 := CPS (gen e6).
    Eval compute in exp2string cc5.
    Eval compute in exp2string (cloconv_exp cc5).
    Eval compute in (compare 200 200 cc5 (cloconv_exp cc5)).

  End Tests.
*)

End ClosureConvert.

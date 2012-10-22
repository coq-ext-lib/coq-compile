Require Import String.
Require Import CoqCompile.Cps CoqCompile.CpsUtil.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Data.Monoid.
Require Import List.
Require Import ExtLib.Functor.Functor.
Require Import ExtLib.Functor.Traversable.
Require Import Data.Strings.
Require Import ExtLib.FMaps.FMaps.
Require Import ExtLib.Decidables.Decidable.

Set Implicit Arguments.
Set Strict Implicit.

Module ClosureConvert.
  Import CPS.
  
  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : Map var env_v}.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {State_m : State nat m}.
    Context {Writer_m : Writer (@Monoid_list_app decl) m}.
    Context {Reader_m : Reader (env_v var) m}.
    Context {Reader_mV : Reader (env_v (op * op)) m}.
    (** I need some way to encapsulate when calls should use a specified environment
     **)

    Import MonadNotation.
    Open Local Scope monad_scope.

    Fixpoint gather_decls (e : decl) : list decl :=
      match e with
        | Rec_d ds => ds
        | d => d :: nil
      end.

    Definition fresh (s : string) : m var :=
      n <- get ;;
      put (S n) ;;
      ret ("_" ++ s ++ @nat2string10 n)%string.

    Definition cloconv_op (o : op) : m op :=
      match o with
        | Var_o v =>
          x <- ask (Reader := Reader_m) ;;
          match FMaps.lookup v x with
            | None => ret o
            | Some v => ret (Var_o v)
          end          
        | Con_o c => ret (Con_o c)
        | Int_o i => ret (Int_o i)
      end.

    Definition liftDecl (d : decl) : m unit :=
      tell (d :: nil).

    Fixpoint underBinders (o : op) (ls : list var) (from : nat) (c : m exp) {struct ls} : m exp :=
      match ls with 
        | nil => c
        | l :: ls => 
          l' <- fresh l ;;
          e <- local (add l l') (underBinders o ls (S from) c) ;;
          ret (Let_e (Prim_d l' Proj_p (Int_o (PreOmega.Z_of_nat' from) :: o :: nil)) e)
      end.
    
    Fixpoint usingEnvForAll (env : op) (ls : list (var * op)) {T} : m T -> m T :=
      local (fold_left (fun acc v => add (fst v) (snd v, env) acc) ls).

    Fixpoint alist_lookup {K V} (R : RelDec (@eq K)) (k : K) (ls : list (K * V)) : option V :=
      match ls with
        | nil => None
        | l :: ls => if eq_dec k (fst l) then Some (snd l) else alist_lookup _ k ls
      end.

    Definition getCustomCall (o : op) : m (option (op * op)) :=
      match o with
        | Var_o v =>
          x <- ask ;;
          ret (FMaps.lookup v x)            
        | _ => ret None
      end.
    
    Fixpoint cloconv_exp' (e : exp) : m exp.
    refine (
      match e with
        | App_e f args =>
          custom <- getCustomCall f ;;
          match custom with
            | Some (f, e) =>
              args <- mapM cloconv_op args ;;
              ret (App_e f (e :: args))
            | None =>
              f <- cloconv_op f ;;
              args <- mapM cloconv_op args ;;
              f_code <- fresh "cptr" ;;
              ret (Let_e (Prim_d f_code Proj_p (Int_o 0 :: f :: nil))
                         (App_e (Var_o f_code) (f :: args)))
          end
        | Let_e (Op_d v o) e =>
          o <- cloconv_op o ;;
          e <- cloconv_exp' e ;;
          ret (Let_e (Op_d v o) e) 
        | Let_e (Prim_d v p os) e =>
          os <- mapM cloconv_op os ;;
          e <- cloconv_exp' e ;;
          ret (Let_e (Prim_d v p os) e) 
        | Let_e (Fn_d v vs e') e =>
          let fvars := free_vars_decl false (Fn_d v vs e') in
          (** fvars does not contain duplicates **)
          envV <- fresh "env"%string ;;
          v_code <- fresh (v ++ "_code")%string ;;
          e' <- underBinders (Var_o envV) fvars 1 (cloconv_exp' e') ;;
          e <- cloconv_exp' e ;;
          liftDecl (Fn_d v_code (envV :: vs) e') ;;
          ret (Let_e (Prim_d v MkTuple_p (Var_o v_code :: map Var_o fvars))
                     e)
        | Let_e (Rec_d ds) e =>
          let ds := gather_decls (Rec_d ds) in
          let func_names := fold_left (fun acc d =>
            match d with
              | Fn_d v _ _ => v :: acc
              | _ => acc
            end) ds nil in
          (** Find all the functions and get the combined environment **)
          let env := monoid_sum Monoid_list_union
            (map (fun d => 
              match d with 
                | Fn_d v vs e => free_vars_decl true (Fn_d v vs e)  
                | _ => monoid_unit Monoid_list_union
              end) ds)
          in
          (** Remove the recursive functions from the environment **)
          let env := filter (fun x => negb (anyb (eq_dec x) func_names)) env in
          (** The names for the code **)
          funcCodeNames <- mapM (fun n => 
            v <- fresh (n ++ "_code") ;; 
            vw <- fresh (n ++ "_wrap_code") ;; 
            ret (n, (v, vw))) func_names ;;
          let funcCodeOps := map (fun x => let '(a,(b,_)) := x in (a, Var_o b)) funcCodeNames in
          (** Lift the functions & wrappers out **)
          mapM (fun d =>
            match d with
              | Fn_d v vs e =>
                envV <- fresh "env" ;;
                e <- usingEnvForAll (Var_o envV) funcCodeOps (underBinders (Var_o envV) env 0 (cloconv_exp' e)) ;;
                match alist_lookup _ v funcCodeNames with
                  | None => ret tt (** Dead Code **)
                  | Some (cptr, cptr_wrap) =>
                    liftDecl (Fn_d cptr (envV :: vs) e) ;;
                    zV <- fresh "env" ;;
                    liftDecl (Fn_d cptr_wrap (envV :: vs) 
                                   (Let_e (Prim_d zV Proj_p (Int_o (PreOmega.Z_of_nat' 1) :: Var_o envV :: nil))
                                          (App_e (Var_o cptr) (Var_o zV :: map Var_o vs))))
                end
              | _ => ret tt
            end) ds ;;
          (** Construct non-functions & wrapper closures **)
          all_envV <- fresh "env" ;;
          let all_env_d := Prim_d all_envV MkTuple_p (map Var_o env) in
          ds' <- mapM (fun d =>
            match d with
              | Fn_d v _ _ =>
                match alist_lookup _ v funcCodeNames with
                  | None => ret (Op_d ""%string (Var_o ""%string)) (** Dead Code **)
                  | Some (_, cptr_wrap) =>
                    ret (Prim_d v MkTuple_p (Var_o cptr_wrap :: Var_o all_envV :: nil))
                end
              | Prim_d v p os =>
                os <- mapM cloconv_op os ;;
                ret (Prim_d v p os)
              | Rec_d _ => ret (Rec_d nil) (** Dead Code **)
              | Op_d v o =>
                o <- cloconv_op o ;;
                ret (Op_d v o)
            end) ds ;;
          (** Cps the result **)
          e <- cloconv_exp' e ;;
          (** Return everything **)
          ret (Let_e (Rec_d (all_env_d :: ds')) e)
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
        | Halt_e o =>
          o <- cloconv_op o ;;
          ret (Halt_e o)
      end).
  Defined.
    
  End monadic.
  
  End maps.

  Require Import ExtLib.FMaps.FMapAList.
  Require Import ExtLib.Monad.WriterMonad.
  Require Import ExtLib.Monad.ReaderMonad.
  Require Import ExtLib.Monad.StateMonad.

  Definition cloconv_exp (e : exp) : exp :=
    let env_v := alist var in
    let c := cloconv_exp' (env_v := env_v) (m := readerT (env_v var) (readerT (env_v (op * op)%type) (writerT (@Monoid_list_app decl) (state nat)))) e in
    let '(e', ds', _) := runState (runWriterT (runReaderT (runReaderT c empty) empty)) 0 in
    Let_e (Rec_d ds') e'.

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

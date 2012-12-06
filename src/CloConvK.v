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
Require Import ExtLib.Data.Map.FMapAList.

Set Implicit Arguments.
Set Strict Implicit.

Module ClosureConvert.
  Import CPSK.

  Section maps.
    Variable env_v : Type -> Type.
    Context {Mv : DMap var env_v}.
    Variable env_k : Type -> Type.
    Context {Mk : DMap cont env_k}.

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {State_m : MonadState positive m}.
    Context {Writer_m : MonadWriter (@Monoid_list_app decl) m}.
    Context {Reader_m : MonadReader (env_v op) m}.
    Context {Reader_k : MonadReader (env_k cont) m}.
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

    Definition freshCont (k : cont) : m cont :=
      n <- modify Psucc ;;
      let '(K v _) := k in
      ret (K v n).

    Definition cloconv_op (o : op) : m op :=
      match o with
        | Var_o v =>
          x <- ask (MonadReader := Reader_m) ;;
          match Maps.lookup v x with
            | None => raise ("Variable " ++ (to_string o) ++ " not found")%string
            | Some v => ret v
          end          
        | Con_o _ => ret o
        | Int_o _ => ret o
        | InitWorld_o => ret o
      end.

    Definition cloconv_k (k : cont) : m cont := 
      x <- asks (Maps.lookup k) ;;
      match x with
        | None => raise ("Continuation " ++ (to_string k) ++ " not found")%string
        | Some k => ret k
      end.

    Definition liftDecl (d : decl) : m unit :=
      tell (d :: nil).

    (** unpack the environment stored in [o]. The variable names are in [ls] and the index of the
     ** first is [from]. Run [c] under all the binders.
     **)
    Fixpoint unpackEnv (o : op) (ls : list var) (from : nat) (c : m exp) {struct ls} : m exp :=
      match ls with 
        | nil => c
        | l :: ls => 
          l' <- freshFor l ;;
          e <- local (Maps.add l (Var_o l')) (unpackEnv o ls (S from) c) ;;
          ret (Let_e (Prim_d l' Proj_p (Int_o (PreOmega.Z_of_nat' from) :: o :: nil)) e)
      end.

    Definition withVars {T} (ls : list var) (os : list var) : m T -> m T :=
      local (fold_left (fun mp vo => Maps.add (fst vo) (Var_o (snd vo)) mp) (List.combine ls os)).

    Definition withVar {T} (v : var) (v' : var) : m T -> m T :=
      withVars (v :: nil) (v'::nil).

    Definition withConts {T} (ls ls' : list cont) : m T -> m T :=
      local (fold_left (fun mp vo => Maps.add (fst vo) (snd vo) mp) (List.combine ls ls')).

    (** Build closures for all of [func_names] using [code_names] for the function pointers
     ** and [env] for the environment pointer. Run [c] under fresh binders.
     **)
    Fixpoint buildClosures (envF : op) (func_names code_names : list var) (c : m exp) : m exp :=
      match func_names , code_names with
        | nil , nil => c
        | name :: func_names , codeF :: code_names => 
          zF <- freshFor name ;;
          e <- withVar name zF (buildClosures envF func_names code_names c) ;;
          ret (Let_e (Prim_d zF MkTuple_p (Var_o codeF :: envF :: nil)) e)
        | _ , _ => 
          raise "Bug, got different list sizes to buildClosures"%string
      end.

    (** TODO: Move to library **)
    Fixpoint filter_map {A B} (f : A -> option B) (ls : list A) : list B :=
      match ls with
        | nil => nil
        | l :: ls => 
          match f l with
            | None => filter_map f ls
            | Some v => v :: filter_map f ls
          end
      end.

    Fixpoint cloconv_exp' (e : exp) : m exp.
    Set Printing Implicit.
    refine (
      match e with
        | AppK_e k args =>
          args <- mapM cloconv_op args ;;
          k <- cloconv_k k ;;
          ret (AppK_e k args)
        | LetK_e ks e =>
          let k_names := map (fun x => let '(k,_,_) := x in k) ks in
          ksF <- mapM freshCont k_names ;;
          withConts k_names ksF (
            ks <- mapM (fun k_xs_e => let '(k,xs,e) := k_xs_e in
                          kF <- cloconv_k k ;;
                          xsF <- mapM freshFor xs ;;
                          e <- withVars xs xsF (cloconv_exp' e) ;;
                          ret (kF, xsF, e)) ks ;;
            e <- cloconv_exp' e ;;
            ret (LetK_e ks e)
          )
        | App_e f ks args =>
          fF <- cloconv_op f ;;
          ksF <- mapM cloconv_k ks ;;
          argsF <- mapM cloconv_op args ;;
          f_codeF <- fresh "cptr" ;;
          ret (Let_e (Prim_d f_codeF Proj_p (Int_o 0 :: fF :: nil))
                     (App_e (Var_o f_codeF) ksF (fF :: argsF)))
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
          v' <- freshFor v ;;
          o <- cloconv_op o ;;
          e <- withVar v v' (cloconv_exp' e) ;;
          ret (Let_e (Op_d v' o) e)
        | Let_e (Prim_d v p os) e =>
          v' <- freshFor v ;;
          os <- mapM cloconv_op os ;;
          e <- withVar v v' (cloconv_exp' e) ;;
          ret (Let_e (Prim_d v' p os) e) 
        | Let_e (Bind_d x w m os) e =>
          x' <- freshFor x ;;
          w' <- freshFor w ;;
          os <- mapM cloconv_op os ;;
          e <- withVars (x :: w :: nil) (x' :: w' :: nil) (cloconv_exp' e) ;;
          ret (Let_e (Bind_d x' w' m os) e) 
        | Let_e (Fn_d v ks vs e') e =>
          let fvars : lset (@eq (var + cont)) := free_vars_decl false (Fn_d v ks vs e') in
          fvars <- mapM (fun v' =>
            match v' with
              | inl v => ret v
              | inr x => 
                raise ("Invariant violation: escaping continuation " ++ to_string x ++ " from " ++ to_string v)%string
            end) fvars ;;
          ks' <- mapM freshCont ks ;;
          vs' <- mapM freshFor vs ;;
          (** fvars does not contain duplicates **)
          envV <- fresh "env"%string ;;
          v_code <- freshFor v ;;
          e' <- unpackEnv (Var_o envV) fvars 1 (withConts ks ks' (withVars vs vs' (cloconv_exp' e'))) ;;
          v' <- freshFor v ;;
          e <- withVar v v' (cloconv_exp' e) ;;
          liftDecl (Fn_d v_code ks' (envV :: vs') e') ;; 
          fvarsF <- mapM cloconv_op (List.map Var_o fvars) ;;
          ret (Let_e (Prim_d v' MkTuple_p (Var_o v_code :: fvarsF))
                     e)
        | Letrec_e ds e_body => _
      end).

    refine (
      (** Check sanity: We don't permit Op_d, Prim_d, or Bind_d in letrec **)
      iterM (fun d => match d with
                        | Fn_d _ _ _ _ => ret tt
                        | Prim_d _ MkTuple_p _ => ret tt
                        | _ => raise ("Invariant violation: found '" ++ to_string d ++ "' in letrec")%string
                      end) ds ;;

      (** Gather the current names **)
      let funcs := filter_map (fun d =>
        match d with
          | Fn_d v ks xs e => Some (v, ks, xs, e)
          | _ => None
        end) ds in
      let tuples := filter_map (fun d =>
        match d with
          | Prim_d v MkTuple_p os => Some (v, os)
          | _ => None
        end) ds in
      let func_names : list var := map (fun v => let '(v,_,_,_) := v in v) funcs in
      let tuple_names : list var := map (fun v => fst v) tuples in
      (** Generate new names for all the declarations **)
      Fcode_names <- mapM freshFor func_names ;;
      let _ : list var := Fcode_names in 

      let funcCodeNames : alist var var := List.combine func_names Fcode_names in
      
      (** Compute the environment **)
      let env : lset (@eq (var + cont)) :=
        fold (fun fn acc => 
          let '(v, ks, xs, e) := fn in          
          Sets.union acc (free_vars_decl true (Fn_d v ks xs e))) Sets.empty funcs
      in
      let env : list var := filter_map (fun x => 
        match x with
          | inl x => 
            if negb (anyb (eq_dec x) func_names) then Some x else None
          | inr x => None
        end) env 
      in

      (** Lift the functions **)
      Fwrap_names <- mapM (fun d =>
        match d with
          | Fn_d v ks vs e =>
            ksF      <- mapM freshCont ks ;;
            vsF      <- mapM freshFor vs ;;
            env_varF <- fresh "env" ;;
            e <- buildClosures (Var_o env_varF) func_names Fcode_names
                 (** for recursive tuples, indexing starts at 0 since the environment is unboxed **)
                 (unpackEnv (Var_o env_varF) env 0 
                 (withConts ks ksF
                 (withVars vs vsF (cloconv_exp' e)))) ;;
            (** get my code name **)
            match Maps.lookup v funcCodeNames with
              | None => raise "Function name not found"%string
              | Some cptr =>
                liftDecl (Fn_d cptr ksF (env_varF :: vsF) e) ;;
                wrapF <- freshFor v ;;
                ksF      <- mapM freshCont ks ;;
                vsF      <- mapM freshFor vs ;;
                env_varF <- fresh "env" ;;
                tmpF     <- fresh "temp" ;;
                liftDecl (Fn_d wrapF ksF (env_varF :: vsF)
                  (Let_e (Prim_d tmpF Proj_p (Int_o (PreOmega.Z_of_nat' 1) :: Var_o env_varF :: nil))
                    (App_e (Var_o cptr) ksF (Var_o tmpF :: map Var_o vsF)))) ;;
                ret (Some wrapF)
            end
          | _ => ret None
        end) ds ;;
      let Fwrap_names : list var := filter_map (fun x => x) Fwrap_names in
      
      Ftuple_names <- mapM freshFor tuple_names ;;
      Fclosure_names <- mapM freshFor func_names ;;

      withVars tuple_names Ftuple_names (withVars func_names Fclosure_names (
        (** Create the environment **)
        env_varF <- fresh "env" ;;
      
        env_decl <- (env_ops <- mapM cloconv_op (List.map Var_o env) ;;
                     ret (Prim_d env_varF MkTuple_p env_ops)) ;;
  
        (** Create the closures **)
        let clos_decls := map (fun clo_wrap => let '(cloF, wrapF) := clo_wrap in
          Prim_d cloF MkTuple_p (Var_o wrapF :: Var_o env_varF :: nil)) (List.combine Fclosure_names Fwrap_names) in

        (** Create the tuples **)
        tpl_decls <- mapM (fun tpl_f => let '((tpl, args), tplF) := tpl_f in
          liftM (Prim_d tplF MkTuple_p) (mapM cloconv_op args)) (List.combine tuples Ftuple_names) ;;

        e <- cloconv_exp' e_body ;;
        ret (Letrec_e (env_decl :: clos_decls ++ tpl_decls) e)
      ))).
    Defined.

  End monadic.
  
  End maps.

  Require Import ExtLib.Data.Monads.WriterMonad.
  Require Import ExtLib.Data.Monads.ReaderMonad.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Monads.EitherMonad.

  Import MonadNotation.
  Local Open Scope monad_scope.
  

  Section monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MExc : MonadExc string m}.

    Definition cloconv_exp (e : exp) : m (list decl * exp) :=
      let env_v := alist var in
      let env_k := alist cont in
      let c := cloconv_exp' (env_v := env_v) (env_k := env_k)
        (m := readerT (env_k cont) (readerT (env_v op) (writerT (@Monoid_list_app decl) (stateT positive m)))) 
        e in
      res <- evalStateT (runWriterT (runReaderT (runReaderT c Maps.empty) Maps.empty)) 1%positive ;;
      let '(e', ds') := res in
      ret (ds', e').
  End monadic.

End ClosureConvert.

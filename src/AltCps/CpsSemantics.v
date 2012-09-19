Require Import Coq.Program.Syntax.
Require Import List.
Open Scope list_scope.
Require Import String.
Open Scope string_scope.

Require Import Lambda.
Import Lambda.

Require Import Fun.
Import FunNotation.
Require Import Functor.
Import FunctorNotation.
Require Import Monad.
Import MonadNotation.
Open Scope monad_scope.
Import MonadPlusNotation.
Require Import Injection.
Require Import Monad.Folds.
Require Import Decidables.Decidable.
Require Import IdentityMonad.
Require Import EitherMonad.
Require Import ReaderMonad.
Require Import Fuel.

Require Import CpsSyntax.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section val.
  Inductive con val := Con
  { conCtor : constructor
  ; conVals : list val
  }.

  Inductive lamClo val := LamClo
  { lamCloArg : var
  ; lamCloKArg : var
  ; lamCloCall : call
  ; lamCloEnv : env_t val
  }.

  Inductive konClo val := KonClo
  { konCloArg : var
  ; konCloCall : call
  ; konCloEnv : env_t val
  }.

  Inductive rec val := Rec
  { recVar : var
  ; recVals : env_t val
  }.

  Inductive val :=
  | ConVal : con val -> val
  | LamVal : lamClo val -> val
  | KonVal : konClo val -> val
  | RecVal : rec val -> val
  .
End val.

Section valHelpers.
  Definition modifyConVals {val} (f:list val -> list val) (c:con val) :=
  {| conCtor := conCtor c
  ;  conVals := f $ conVals c
  |}.

  Definition modifyLamCloEnv {val} (f:env_t val -> env_t val) (l:lamClo val) :=
  {| lamCloArg := lamCloArg l
  ;  lamCloKArg := lamCloKArg l
  ;  lamCloCall := lamCloCall l
  ;  lamCloEnv := f $ lamCloEnv l
  |}.

  Section coercions.
    Context {m:Type->Type} {mMonad:Monad m}.
    Context {e} {eInject:Injection (string * val) e} {mMonadExc:MonadExc e m}.

    Definition coerceCon v : m (con val) :=
    match v with
    | ConVal c => ret c
    | _ => raise (inject ("could not coerce to con", v))
    end.

    Definition coerceKonClo v : m (konClo val) :=
    match v with
    | KonVal kv => ret kv
    | _ => raise (inject ("could not coerce to konClo", v))
    end.

    Definition coerceLamClo v : m (lamClo val) :=
    match v with
    | LamVal lv => ret lv
    | _ => raise (inject ("could not coerce to lamClo", v))
    end.

    Definition coerceRec v : m (rec val) :=
    match v with
    | RecVal rv => ret rv
    | _ => raise (inject ("could not coerce to rec", v))
    end.

  End coercions.
End valHelpers.

Section eval.
  Context {m:Type->Type}.
  Context {mFunctor:Functor m}.
  Context {mMonad:Monad m}.
  Context {mFix:MonadFix m}.
  Context {mPlus:MonadPlus m}.
  Context {e} {mMonadExc:MonadExc e m}.
  Context {eInject1:Injection (string * option val * option (env_t val)) e}.
  Context {eInject2:Injection (string * val) e}.
  Context {eInject3:Injection string e}.
  Context {mReader:Reader (env_t val) m}.

  Definition failWithMsg {A} s : m A :=
  e <- ask ;;
  raise (inject (s, None, Some e))
  .

  Definition failWithVal {A} s v : m A :=
  e <- ask ;;
  raise (inject (s, Some v, Some e))
  .

  Definition evalAtom (o:atom) : m val :=
  match o with
  | VarAtom x =>
      env <- ask ;;
      lookup x env 
  | ConAtom c => ret $ ConVal $ Con c []
  end.

  Definition evalKon (k:kon) : m val := let '(VarKon x) := k in evalAtom $ VarAtom x.

  Fixpoint evalSmall (s:small) : m val :=
  match s with
  | ConSmall c os => ConVal <$> Con c <$> mapM evalAtom os
  | LamSmall x k c => LamVal <$> LamClo x k c <$> ask
  | KonSmall x c => KonVal <$> KonClo x c <$> ask
  end.

  Fixpoint selectPatKon (t:con val) (ks:list (pattern * call)) : m (pattern * call) :=
  match ks with
  | [] => failWithVal "pattern match failure" (ConVal t)
  | k::ks' => 
      let ctor := conCtor t in
      let (p,c) := k in
      match p with
      | Var_p _ => ret k
      | Con_p ctor' _ => if eq_dec ctor ctor' then ret k else selectPatKon t ks'
      end
  end.

  Definition buildRecs xs := map ((fun x => (x, RecVal $ Rec x xs)) <$> fst) xs.

  Definition evalCallME : call -> m val :=
  mfix $ begin fun evalCallME c =>
    let applyKon (k:konClo val) (v:val) : m val :=
      local (const $ update (konCloArg k) v $ konCloEnv k) $
        evalCallME $ konCloCall k
    in
    let applyLam (fv:val) (v:val) (k:val) : m val :=
      f <- coerceLamClo fv <+> coerceRec fv ;;
      match f with
      | inl l =>
          local (const $ update (lamCloArg l) v
                       $ update (lamCloKArg l) k
                       $ lamCloEnv l) $
            evalCallME $ lamCloCall l
      | inr r =>
          let '{| recVar := x ; recVals := xs |} := r in
          l <- coerceLamClo =<< lookup x xs ;;
          let rxs := buildRecs xs in
          local (const $ updateMany rxs
                       $ update (lamCloArg l) v
                       $ update (lamCloKArg l) k
                       $ lamCloEnv l) $
            evalCallME $ lamCloCall l
      end
    in
    let applyPattern (p:pattern) (o:con val) (c:call) : m val :=
      match p with
      | Var_p x => local (update x $ ConVal o) $ evalCallME c
      | Con_p _ xs => local (updateMany $ zip xs $ conVals o) $ evalCallME c
      end
    in
    match c with
    | LetCall b c' =>
        match b with
        | OneBind x sm =>
            v <- evalSmall sm ;;
            local (update x v) (evalCallME c')
        | RecBind xas =>
            xvs <- forEachM xas $ begin fun xa =>
              let (x,s') := xa in
              v <- evalSmall s' ;;
              ret (x,v) 
            end ;;
            let rvs := map (fun x => (x,RecVal $ Rec x xvs)) $ map fst xvs in
            local (updateMany rvs) $ evalCallME c'
        end
    | AppCall f x k =>
        fv <- evalAtom f ;;
        xv <- evalAtom x ;;
        kv <- evalKon k ;;
        applyLam fv xv kv
    | KonCall k x =>
        kv <- coerceKonClo =<< evalKon k ;;
        xv <- evalAtom x ;;
        applyKon kv xv
    | MatchCall o ks =>
        ov <- coerceCon =<< evalAtom o ;;
        pc <- selectPatKon ov ks ;;
        let (p,c) := pc in
        applyPattern p ov c
    | HaltCall o => evalAtom o
    end
  end.

End eval.

Inductive evalError :=
| GasEvalError : evalError
| EvalError : string -> option val -> option (env_t val) -> evalError
. 

Instance evalErrorGasErrorIn : Injection gasError evalError :=
{ inject _e := GasEvalError }.

Instance evalErrorStringIn : Injection string evalError :=
{ inject s := EvalError s None None }.

Instance evalErrorStringValIn : Injection (string * val) evalError :=
{ inject sv := let (s,v) := sv in EvalError s (Some v) None }.

Instance evalErrorStringValEnvIn
  : Injection (string * option val * option (env_t val)) evalError :=
{ inject sve := let '(s,v,e) := sve in EvalError s v e }.

Definition EvalM := fuel $ readerT (env_t val) $ eitherT evalError $ ident.

Definition runEvalM {A} g (m:EvalM A) : evalError + A :=
unIdent (unEitherT (runReaderT (unFuelReaderT m g) [])).

Definition evalCall g := runEvalM g <$> evalCallME.

(*
Import LambdaNotation.
Require Import TrCps.
Eval compute in gen e8.
Eval compute in cps (gen e8).
Eval compute in evalCall 1000 (cps (gen e8)).
*)


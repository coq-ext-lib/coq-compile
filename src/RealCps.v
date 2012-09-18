Require Import String.
Require Import Lambda.
Require Import Monad.
Require Import Monad.Folds.
Require Import List.
Require Import Coq.Program.Syntax.
Require Import Fun.
Require Import Functor.
Require Import ExtLib.Decidables.Decidable.
Require Import Fuel.
Require Import EitherMonad.
Require Import ReaderMonad.
Require Import StateMonad.
Require Import IdentityMonad.

Import Lambda.Lambda.
Import Lambda.LambdaNotation.
Import MonadNotationX.
Import FunNotation.
Import FunctorNotation.

Open Scope string_scope.

Inductive atom :=
| VarAtom : var -> atom
| ConAtom : constructor -> atom
.

Inductive kon := VarKon : var -> kon.

Inductive
small :=
| ConSmall : constructor -> list atom -> small
| LamSmall : var -> var -> call -> small
| KonSmall : list var -> call -> small
with
call :=
| LetSmall  : var -> small -> call -> call
| LetRec    : list (var * small) -> call -> call
| KonCall   : kon -> atom -> call
| AppCall   : list (atom * atom) -> kon -> call
| MatchCall : atom -> list (pattern * call) -> call
| HaltCall  : atom -> call
.

Section Fresh.
  Context {m:Type->Type} {mMonad:Monad m} {mState:State nat m}.

  Definition fresh : m var :=
  x <- get ;;
  put (S x) ;;
  ret $ "$cps$" ++ nat2string x
  .

  Fixpoint freshMany (k:nat) : m (list var) :=
  match k with
  | O => ret []
  | S k' => n <- fresh ;; ns <- freshMany k' ;; ret (n::ns)
  end
  .
End Fresh.

Section CPS.
  Context {m:Type->Type} {mMonad:Monad m} {mState:State nat m}.

  (** apply the object-level function [f] to object-level arguments
  [args], all inside the continuation [k] *)
  Fixpoint applyMany (f:atom) (args:list atom) (k:atom -> m call) : m call :=
  match args with
  | [] => k f
  | o::os =>
      x <- fresh ;;
      c' <- applyMany (VarAtom x) os k ;;
      ok <- fresh ;;
      ret $ LetSmall ok (KonSmall [x] c')
          $ AppCall [(f, o)] (VarKon ok)
  end
  .

  Fixpoint cps (e:exp) (k:atom -> m call) : m call :=
  (* cps a list of expressions *)
  let cpsMany :=
    fix cpsMany (es:list exp) (k:list atom -> m call) : m call :=
    match es with
    | [] => k []
    | e::es => cps e $ fun o => cpsMany es $ fun os => k (o::os)
    end
  in
  (* create a lambda by calling cps with a bound variable *)
  let mkLam (x:var) (e:exp) : m small :=
    kn' <- fresh ;;
    c' <- cps e (fun a => ret $ KonCall (VarKon kn') a) ;;
    ret $ LamSmall x kn' c'
  in
  (* the body of cps... *)
  match e with
  | Var_e x => k $ VarAtom x
  | Lam_e x e1 =>
      l <- mkLam x e1 ;;
      ln <- fresh ;;
      c' <- k (VarAtom ln) ;;
      ret $ LetSmall ln l c'
  | App_e e1 e2 =>
      cps e1 $ begin fun a1 =>
        cps e2 $ begin fun a2 =>
          x <- fresh ;;
          match a1 with
          | ConAtom t =>
              c <- k (VarAtom x) ;;
              ret $ LetSmall x (ConSmall t [a2]) c
          | VarAtom f =>
              obk <- k (VarAtom x) ;;
              ok <- fresh ;;
              ret $ LetSmall ok (KonSmall [x] obk)
                  $ AppCall [(a1, a2)] (VarKon ok)
          end
        end
      end
  | Let_e x e1 e2 =>
      cps e1 $ begin fun a =>
        c2 <- cps e2 k ;;
        ok <- fresh ;;
        ret $ LetSmall ok (KonSmall [x] c2)
            $ KonCall (VarKon ok) a
      end
  | Con_e t es =>
      cpsMany es $ begin fun aes =>
        x <- fresh ;;
        c <- k (VarAtom x) ;;
        ret $ LetSmall x (ConSmall t aes) c
      end
  | Match_e e1 pes =>
      cps e1 $ begin fun a =>
        kn <- fresh ;;
        pcs <- forEachM pes $ begin fun pe =>
          let (p,e') := pe in
          c' <- cps e' (fun a' => ret $ KonCall (VarKon kn) a') ;;
          ret $ (p,c')
        end ;;
        x <- fresh ;;
        ke <- k (VarAtom x) ;;
        ret $ LetSmall kn (KonSmall [x] ke) $ MatchCall a pcs
      end
  | Letrec_e nlams e1 =>
      nalams <- forEachM nlams begin fun nlam =>
          let '(n, (fn, e')) := nlam in
          l <- mkLam fn e' ;;
          ret $ (n, l)
      end ;;
      c <- cps e1 k ;; 
      ret $ LetRec nalams c
  end
  .
End CPS.

Definition CPSM := stateT nat ident.
Definition runCPSM {A} s (m:CPSM A) := unIdent (runStateT m s).
Definition cpsM (e:exp) (k:atom -> CPSM call) : CPSM call := cps e k.
Definition runCPS (i:nat) (e:exp) (k:atom -> call) : call :=
fst (runCPSM i (cpsM e (fun a => ret (k a)))).

Class HasStuckError val e :=
{ stuckError : string -> option val -> option (env_t val) -> e
}.

Section Semantics.
  Context {m:Type->Type}.
  Context {mFunctor:Functor m}.
  Context {mMonad:Monad m} {mFix:MonadFix m} {mZero:Zero m}.

  Inductive con val := Con
  { conCtor : constructor
  ; conVals : list val
  }
  .
  Implicit Arguments conCtor [val].
  Implicit Arguments conVals [val].
  Definition modifyConVals {val} (f:list val -> list val) (c:con val) :=
  {| conCtor := conCtor c
  ;  conVals := f $ conVals c
  |}.
  Implicit Arguments Con [val].
  Implicit Arguments conCtor [val].
  Implicit Arguments conVals [val].

  Inductive lamClo val := LamClo
  { lamCloArg : var
  ; lamCloKArg : var
  ; lamCloCall : call
  ; lamCloEnv : env_t val
  }
  .
  Implicit Arguments LamClo [val].
  Implicit Arguments lamCloArg [val].
  Implicit Arguments lamCloKArg [val].
  Implicit Arguments lamCloCall [val].
  Implicit Arguments lamCloEnv [val].
  Definition modifyLamCloEnv {val} (f:env_t val -> env_t val) (l:lamClo val) :=
  {| lamCloArg := lamCloArg l
  ;  lamCloKArg := lamCloKArg l
  ;  lamCloCall := lamCloCall l
  ;  lamCloEnv := f $ lamCloEnv l
  |}.

  Inductive lamVal val :=
  | CloLamVal : lamClo val -> lamVal val
  | RecLamVal : var -> env_t val -> lamVal val
  .
  Implicit Arguments CloLamVal [val].
  Implicit Arguments RecLamVal [val].

  Inductive konClo val := KonClo
  { konCloArgs : list var
  ; konCloCall : call
  ; konCloEnv : env_t val
  }
  .
  Implicit Arguments KonClo [val].
  Implicit Arguments konCloArgs [val].
  Implicit Arguments konCloCall [val].
  Implicit Arguments konCloEnv [val].

  Inductive val :=
  | ConVal : con val -> val
  | LamVal : lamVal val -> val
  | KonCloVal : konClo val -> val
  .

  Context {e} {mMonadExc:MonadExc e m} {eHasStuckError:HasStuckError val e}.
    
  Definition coerceCon v : m (con val) :=
  match v with
  | ConVal c => ret c
  | _ => zero
  end
  .

  Definition coerceKonClo v : m (konClo val) :=
  match v with
  | KonCloVal kv => ret kv
  | _ => zero
  end
  .

  Definition coerceLamVal v : m (lamVal val) :=
  match v with
  | LamVal lv => ret lv
  | _ => zero
  end
  .

  Definition coerceLamClo v : m (lamClo val) :=
  v' <- coerceLamVal v ;;
  match v' with
  | CloLamVal l => ret l
  | _ => zero
  end
  .

  Context {mReader:Reader (env_t val) m}.

  Definition evalAtom (o:atom) : m val :=
  match o with
  | VarAtom x =>
      env <- ask ;;
      let vM := lookup env x in
      match vM with
      | None => raise (stuckError ("env lookup:"++x) None (Some env))
      | Some v => ret v
      end
  | ConAtom c => ret $ ConVal $ Con c []
  end
  .

  Definition evalKon (k:kon) : m val :=
  match k with VarKon x => evalAtom (VarAtom x) end.

  Fixpoint evalSmall (s:small) : m val :=
  match s with
  | ConSmall c os => ConVal <$> Con c <$> mapM evalAtom os
  | LamSmall x k c => LamVal <$> @CloLamVal _ <$> LamClo x k c <$> ask
  | KonSmall x c => KonCloVal <$> KonClo x c <$> ask
  end
  .

  Fixpoint selectPatKon (t:con val) (ks:list (pattern * call)) : m (pattern * call) :=
  match ks with
  | [] => zero
  | k::ks' => 
      let ctor := conCtor t in
      let (p,c) := k in
      match p with
      | Var_p _ => ret k
      | Con_p ctor' _ => if eq_dec ctor ctor' then ret k else selectPatKon t ks'
      end
  end
  .

  Local Open Scope list_scope.
        
  Definition evalCall : call -> m val :=
  mfix $ begin fun evalCall c =>
    let applyKon (k:konClo val) (vs:list val) : m val :=
      local (const $ updateMany (zip (konCloArgs k) vs) $ konCloEnv k) $
        evalCall $ konCloCall k
    in
    let applyLams (fvs:list (lamVal val * val)) (k:konClo val) : m val :=
      vs <- forEachM fvs $ begin fun fv =>
        let (f,v) := fv in
        match f with
        | CloLamVal l =>
            local (const $ update (lamCloArg l) v (lamCloEnv l)) $
              evalCall $ lamCloCall l
        | RecLamVal x xs =>
            let lvM := lookup xs x in
            v <- match lvM with
              | None => zero
              | Some lv =>
                l <- coerceLamClo lv ;;
                local (const $ update x (LamVal (RecLamVal x xs))
                             $ update (lamCloArg l) v
                             $ lamCloEnv l) $
                  evalCall $ lamCloCall l
            end ;;
            applyKon k [v]
        end
      end ;;
      applyKon k vs
    in
    let applyPattern (p:pattern) (o:con val) (c:call) : m val :=
      match p with
      | Var_p x => local (update x (ConVal o)) (evalCall c)
      | Con_p _ xs => local (updateMany (zip xs (conVals o))) (evalCall c)
      end
    in
    match c with
    | LetSmall x sm c' =>
        v <- evalSmall sm ;;
        local (update x v) (evalCall c')
    | LetRec xas c' =>
        xvs <- forEachM xas $ begin fun xs =>
          let (x,s') := xs in
          v <- evalSmall s' ;;
          ret (x,v) 
        end ;;
        let rvs := map (fun x => (x,LamVal $ RecLamVal x xvs)) (map fst xvs) in
        local (updateMany rvs) (evalCall c')
    | KonCall k x =>
        kv <- coerceKonClo =<< evalKon k ;;
        xv <- evalAtom x ;;
        applyKon kv [xv]
    | AppCall fxs k =>
        fvs <- forEachM fxs $ begin fun fx =>
          let (f,x) := fx in
          fv <- coerceLamVal =<< evalAtom f ;;
          xv <- evalAtom x ;;
          ret (fv,xv)
        end ;;
        kv <- coerceKonClo =<< evalKon k ;;
        applyLams fvs kv
    | MatchCall o ks =>
        ov <- coerceCon =<< evalAtom o ;;
        pc <- selectPatKon ov ks ;;
        let (p,c) := pc in
        applyPattern p ov c
    | HaltCall o => evalAtom o
    end
  end
  .

End Semantics.

Inductive evalError :=
| GasError : evalError
| StuckError : string -> option val -> option (env_t val) -> evalError
. 

Instance EvalErrorHasGasError : HasGasError evalError := { gasError := GasError }.
Instance EvalErrorHasStuckError : HasStuckError val evalError :=
{ stuckError := StuckError }.

Instance EitherTEvalErrorZero {m} {mMonad:Monad m} : Zero (eitherT evalError m) :=
{ zero := _ }. apply raise ; apply (StuckError "" None None). Defined.

Definition M := fuel $ readerT (env_t val) $ eitherT evalError $ ident.

Definition runM {A} g e (m:M A) : evalError + A :=
unIdent (unEitherT (runReaderT (unFuelReaderT m g) e)).

Definition evalCallM (c:call) : M val := evalCall c.

Definition runEvalCall g e c := runM g e (evalCallM c).

(*
Eval compute in gen e1.
Eval compute in runCPS O (gen e1) HaltCall.
Eval compute in runEvalCall 1000 [] (runCPS O (gen e1) HaltCall).
Eval compute in runEvalCall 1000 [] (runCPS O (gen e2) HaltCall).
Eval compute in runEvalCall 1000 [] (runCPS O (gen e3) HaltCall).
Eval compute in gen e4.
Eval compute in runCPS O (gen e4) HaltCall.
Eval compute in runEvalCall 1000 [] (runCPS O (gen e4) HaltCall).
Eval compute in gen e8.
Eval compute in runCPS O (gen e8) HaltCall.
Eval compute in runEvalCall 1000 [] (runCPS O (gen e8) HaltCall).
*)


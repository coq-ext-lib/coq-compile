Require Import Coq.Program.Syntax.
Require Import List.
Open Scope list_scope.
Require Import String.

Require Import Lambda.
Import Lambda.
Definition nat2string := LambdaNotation.nat2string.

Require Import Monad.
Import MonadNotation.
Open Scope monad_scope.
Require Import Functor.
Import FunctorNotation.
Require Import Fun.
Import FunNotation.
Require Import StateMonad.
Require Import IdentityMonad.
Require Import Monad.Folds.

Require Import CpsSyntax.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section fresh.
  Context {m:Type->Type} {mMonad:Monad m} {mState:State nat m}.

  Local Open Scope string_scope.
  Definition fresh : m var :=
  x <- get ;;
  put (S x) ;;
  ret $ "$cps$" ++ nat2string x
  .

  Fixpoint freshMany (k:nat) : m (list var) :=
  match k with
  | O => ret []
  | S k' => n <- fresh ;; ns <- freshMany k' ;; ret (n::ns)
  end.
End fresh.


Section cpsMK.
  Context {m:Type->Type} {mMonad:Monad m} {mState:State nat m}.

  Definition mkLetApp (x:var) (f:atom) (o:atom) (c:call) : m call :=
  k <- fresh ;;
  ret $ LetCall (OneBind k (KonSmall x c)) $ AppCall f o (VarKon k)
  .

  Fixpoint applyMany (f:atom) (args:list atom) (k:atom -> m call) : m call :=
  match args with
  | [] => k f
  | o::os =>
      x <- fresh ;;
      c <- applyMany (VarAtom x) os k ;;
      mkLetApp x f o c
  end.

  Definition reifyK (mk:atom -> m call) : m small :=
  x <- fresh ;;
  c <- mk (VarAtom x) ;;
  ret $ KonSmall x c
  .

  Fixpoint cpsMK (e:exp) (mk:atom -> m call) : m call :=
  (* cps a list of expressions *)
  let cpsMany :=
    fix cpsMany (es:list exp) (mk:list atom -> m call) : m call :=
    match es with
    | [] => mk []
    | e::es => cpsMK e $ fun o => cpsMany es $ fun os => mk (o::os)
    end
  in
  (* create a lambda by calling cps with a bound variable *)
  let mkLam (x:var) (e:exp) : m small :=
    kn' <- fresh ;;
    c' <- cpsMK e (fun a => ret $ KonCall (VarKon kn') a) ;;
    ret $ LamSmall x kn' c'
  in
  (* the body of cps... *)
  match e with
  | Var_e x => mk $ VarAtom x
  | Lam_e x e1 =>
      x <- fresh ;;
      l <- mkLam x e1 ;;
      c <- mk (VarAtom x) ;;
      ret $ LetCall (OneBind x l) c
  | App_e e1 e2 =>
      cpsMK e1 $ begin fun a1 =>
        cpsMK e2 $ begin fun a2 =>
          k <- reifyK mk ;;
          kn <- fresh ;;
          ret $ LetCall (OneBind kn k) $ AppCall a1 a2 (VarKon kn)
        end
      end
  | Let_e x e1 e2 =>
      cpsMK e1 $ begin fun a =>
        c <- cpsMK e2 mk ;;
        kn <- fresh ;;
        ret $ LetCall (OneBind kn $ KonSmall x c) $ KonCall (VarKon kn) a
      end
  | Con_e t es =>
      cpsMany es $ begin fun aes =>
        x <- fresh ;;
        c <- mk (VarAtom x) ;;
        ret $ LetCall (OneBind x $ ConSmall t aes) c
      end
  | Match_e e1 pes =>
      cpsMK e1 $ begin fun a =>
        kn <- fresh ;;
        pcs <- forEachM pes $ begin fun pe =>
          let (p,e') := pe in
          c' <- cpsMK e' (fun a' => ret $ KonCall (VarKon kn) a') ;;
          ret $ (p,c')
        end ;;
        k <- reifyK mk ;;
        ret $ LetCall (OneBind kn k) $ MatchCall a pcs
      end
  | Letrec_e nlams e1 =>
      nalams <- forEachM nlams begin fun nlam =>
          let '(n, (fn, e')) := nlam in
          l <- mkLam fn e' ;;
          ret $ (n, l)
      end ;;
      c <- cpsMK e1 mk ;; 
      ret $ LetCall (RecBind nalams) c
  end.

  Definition cpsM e := cpsMK e (ret <$> HaltCall).

End cpsMK.

Definition CpsM := stateT nat ident.
Definition runCpsM {A} (m:CpsM A) := fst $ unIdent $ runStateT m O.
Definition cps := runCpsM <$> cpsM.

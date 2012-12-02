Require Import String List Bool.
Require Import CoqCompile.CpsK CoqCompile.Analyze.AbstractDomains.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Map.FMapAList.

Import CpsK.CPSK.

Section AI.
  Variables D C V : Type.
  Context {AbsTime_C  : AbsTime C}.
  Context {AbsValue_V : AbsDomain D V C (var + cont)}.
  Context {IntValue_V : IntValue V}.
  Context {BoolValue_V : BoolValue V}.
  Context {CtorValue_V  : CtorValue V constructor}.
  Context {FnValue_V  : FnValue V C D}.
  Context {TplValue_V : TplValue V}.

  Import MonadNotation.
  Local Open Scope monad_scope.
  Local Open Scope list_scope.
     
  Section Monadic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Exc_m : MonadExc string m}.
    Context {Fix_m : MonadFix m}.
    (** DFS **)
    Context {State_m : MonadState (alist (C * exp) D) m}.

    Definition eval_op (o : op) (ctx : C) (dom : D) : m V :=
      match o with
        | Var_o v =>
          ret (lookup ctx (inl v) dom)
        | Con_o c => ret bottomA (** TODO: Not done **)
        | Int_o i => ret (injInt (Some i))
        | InitWorld_o => ret bottomA (** TODO: ?? **)
      end.
    
    Definition illFormed_decl {A} (d : decl) : m A :=
      raise ("Ill-formed declaration " ++ runShow (show d))%string.

    Definition eval_decl (d : decl) (ctx : C) (dom : D) : m D :=
      v_vA <- 
      match d return m (list (var * V)) with
        | Op_d v o =>
          oA <- eval_op o ctx dom ;;
          ret ((v, oA) :: nil)
            
        | Prim_d v p os => 
          argsA <- mapM (fun x => eval_op x ctx dom) os ;;
          vA <- match p , argsA with
                  | Eq_p , l :: r :: nil =>
                    ret (injBool (eqA l r))
                  | Neq_p , l :: r :: nil =>
                    ret (injBool (map negb (eqA l r)))
                  | Lt_p , l :: r :: nil =>
                    ret (injBool (ltA l r))
                  | Lte_p , l :: r :: nil =>
                    ret (orA (injBool (ltA l r)) (injBool (eqA l r)))
                  | Ptr_p , l :: nil => ret (injBool None) (** ?? **)
                  | Plus_p , l :: r :: nil => ret (plusA l r)
                  | Minus_p , l :: r :: nil => ret (minusA l r)
                  | Times_p , l :: r :: nil => ret (timesA l r)
                  | MkTuple_p , argsA => ret (injTuple argsA)
                  | Proj_p , l :: r :: nil => ret (projA l r)
                  | _ , _ => illFormed_decl (Prim_d v p os)
                end ;;
          ret ((v, vA) :: nil)

        | Fn_d v ks args body =>
          ret ((v, injFn ctx ks args body) :: nil)
          
        | Bind_d v1 v2 m os =>
          ret ((v1, topA) :: (v2, topA) :: nil)
      end ;;
      let dom' := fold_left (fun dom v_vA => let '(v, vA) := v_vA in
        update ctx (inl v) vA dom) v_vA dom in
      ret dom'.

    Definition init_decl (d : decl) (ctx : C) (dom : D) : D :=
      match d with
        | Op_d v _ 
        | Prim_d v _ _
        | Fn_d v _ _ _ => 
          update ctx (inl v) bottomA dom
        | Bind_d v1 v2 _ _ =>
          let dom := update ctx (inl v1) bottomA dom in
            update ctx (inl v2) bottomA dom
      end.
      
    Definition aeval_exp : C -> D -> exp -> m D :=
      mfix3 _ (fun aeval => fun (ctx : C) (dom : D) (e : exp) =>
        memo <- gets (Maps.lookup (ctx, e)) ;;
        let stop :=
          match memo with
            | None => false
            | Some dom' => dom_leq dom dom'
          end
        in
        if stop then ret dom
        else
          (fix recur (ctx : C) (dom : D) (e : exp) : m D :=
            match e return m D with
              | App_e o ks os =>
                let argsK := List.map (fun k => lookup ctx (inr k) dom) ks in
                fA <- eval_op o ctx dom ;;
                argsA <- mapM (fun x => eval_op x ctx dom) os ;;
                applyA aeval dom fA argsK argsA 
              | Let_e d e =>
                dom' <- eval_decl d ctx dom ;;
                recur ctx dom' e
              | AppK_e k os =>
                let fA := lookup ctx (inr k) dom in
                argsA <- mapM (fun x => eval_op x ctx dom) os ;;
                applyA aeval dom fA nil argsA 
              | LetK_e ks e =>
                let dom' := 
                  fold_left (fun dom kxse => let '(k,xs,e) := kxse in
                    update ctx (inr k) (injFn ctx nil xs e) dom) ks dom in
                recur ctx dom' e
              | Letrec_e ds e =>
                let dom_init := 
                  fold_left (fun dom d => init_decl d ctx dom) ds dom in
                dom' <- foldM (fun d dom => eval_decl d ctx dom) (ret dom_init) ds ;;
                recur ctx dom' e
              | Switch_e o arms e =>
                s <- eval_op o ctx dom ;;
                dom' <- foldM (fun x dom => 
                  ctx <- ret ctx ;;
                  recur ctx dom (snd x)) (ret dom) arms ;;
                match e with
                  | Some e =>
                    recur ctx dom' e
                  | None => ret dom'
                end
              | Halt_e o1 o2 =>
                ret dom
            end) ctx dom e).
    
  End Monadic.

  Require Import ExtLib.Data.Monads.EitherMonad.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Monads.FuelMonad.

  Section interface.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MonadFix_m : MonadFix m}.

    Arguments aeval_exp {m} {_ _ _ _} ctx dom e.

    Definition aeval (ctx : C) (dom : D) (e : exp) : m (string + D) :=
      let c := aeval_exp (m := eitherT string (stateT (alist (C * exp) D) m)) ctx dom e in 
      evalStateT (unEitherT c) Maps.empty.
  End interface.

End AI.

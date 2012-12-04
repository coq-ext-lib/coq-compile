Require Import String List Bool.
Require Import CoqCompile.CpsK CoqCompile.Analyze.AbstractDomains.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Map.FMapAList.
Require Import CoqCompile.TraceMonad.

Import CpsK.CPSK.

Set Implicit Arguments.
Set Strict Implicit.

Section AI.
  Variables D C V : Type.
  Context {AbsTime_C  : AbsTime C}.
  Context {AbsValue_V : AbsDomain C D (var + cont) V}.
  Context {IntValue_V : IntValue V}.
  Context {BoolValue_V : BoolValue V}.
  Context {CtorValue_V  : CtorValue V constructor}.
  Context {FnValue_V  : FnValue C D (var + cont) V}.
  Context {TplValue_V : TplValue C D V}.
  Context {Show_C : Show C}.
  Context {Show_D : Show D}.
  Context {Show_V : Show V}.

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
    Context {Trace_m : MonadTrace string m}.

    Definition eval_op (o : op) (ctx : C) (dom : D) : m V :=
      match o with
        | Var_o v =>
          ret (lookup ctx (inl v) dom)
        | Con_o c => ret (injCtor c) 
        | Int_o i => ret (injInt (Some i))
        | InitWorld_o => ret bottomA (** TODO: ?? **)
      end.
    
    Definition illFormed_decl {A} (d : decl) : m A :=
      raise ("Ill-formed declaration " ++ runShow (show d))%string.

    Definition eval_decl (d : decl) (ctx : C) (dom : D) : m D :=
      match d with
        | Prim_d v Mk_tuple os =>
          argsA <- mapM (fun x => eval_op x ctx dom) os ;;
          ret (injTuple dom ctx v argsA)
        | _ =>
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
                      | Proj_p , l :: r :: nil => ret (projA dom l r)
                      | _ , _ => illFormed_decl (Prim_d v p os)
                    end ;;
              ret ((v, vA) :: nil)
              
            | Fn_d v ks args body =>
              ret ((v, injFn ctx (inl v) ks args body) :: nil)
              
            | Bind_d v1 v2 m os =>
              ret ((v1, topA) :: (v2, topA) :: nil)
          end ;;
          let dom' := fold_left (fun dom v_vA => let '(v, vA) := v_vA in
            update ctx (inl v) vA dom) v_vA dom in
          ret dom'
      end.

    Local Open Scope string_scope.

    Definition aeval_exp : C -> D -> exp -> m D :=
      mfix3 _ (fun aeval => fun (ctx : C) (dom : D) (e : exp) =>
        memo <- gets (Maps.lookup (ctx, e)) ;;
        let stop :=
          match memo with
            | None => false
            | Some dom' => dom_leq dom dom'
          end
        in
        mlog ("call to aeval " ++ to_string stop ++ (String Char.chr_newline EmptyString) ++
              "dom = " ++ to_string dom ++ (String Char.chr_newline EmptyString) ++
              "dom' = " ++ match memo with
                             | None => "NONE"
                             | Some memo => to_string memo
                           end ++ (String Char.chr_newline EmptyString))%string ;;
        if stop then 
          match memo with
            | None => mlog "bug"%string ;; ret dom
            | Some dom' => ret dom'
          end
        else
          let dom := match memo with
                       | None => dom
                       | Some dom' => joinA dom dom'
                     end in
          modify (Maps.add (ctx, e) dom) ;;
          MAP <- get ;;
          let len : nat := length MAP in
          mlog ("adding stuff to map " ++ to_string (len)) ;;
          (fix recur (ctx : C) (dom : D) (e : exp) : m D :=
            match e return m D with
              | App_e o ks os =>
                let argsK := List.map (fun k => lookup ctx (inr k) dom) ks in
                fA <- eval_op o ctx dom ;;
                argsA <- mapM (fun x => eval_op x ctx dom) os ;;
                mlog ("applying " ++ to_string fA) ;;
                applyA aeval dom fA argsK argsA 
              | Let_e d e =>
                dom' <- eval_decl d ctx dom ;;
                recur ctx dom' e
              | AppK_e k os =>
                let fA := lookup ctx (inr k) dom in
                argsA <- mapM (fun x => eval_op x ctx dom) os ;;
                mlog ("applying K " ++ to_string fA) ;;
                applyA aeval dom fA nil argsA 
              | LetK_e ks e =>
                let dom' := 
                  fold_left (fun dom kxse => let '(k,xs,e) := kxse in
                    update ctx (inr k) (injFn ctx (inr k) nil xs e) dom) ks dom in
                recur ctx dom' e
              | Letrec_e ds e =>
                dom' <- 
                mfix (fun go => fun (dom : D) =>
                  dom' <- foldM (fun d acc => eval_decl d ctx acc) (ret dom) ds ;;
                  if dom_leq dom' dom then ret dom' else go dom') dom ;;
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
                mlog "got to halt"%string ;;
                ret dom
            end) ctx dom e).
    
  End Monadic.

  Require Import ExtLib.Data.Monads.EitherMonad.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Monads.FuelMonad.
  Require Import ExtLib.Data.Monads.IdentityMonad.

  Arguments aeval_exp {m} {_ _ _ _ _} ctx dom e.
  
  Section interface.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MonadTrace_m : MonadTrace string m}.

    Require Import BinNums.
    Definition aeval (ctx : C) (dom : D) (e : exp) (fuel : N) : m (string + D) :=
      let c := aeval_exp (m := GFixT (eitherT string (stateT (alist (C * exp) D) m))) ctx dom e in 
      bind (evalStateT (unEitherT (runGFixT c fuel)) Maps.empty) (fun res => 
      match res with
        | inl err => ret (inl err)
        | inr None => ret (inl "aeval: out of fuel")%string
        | inr (Some dom) => ret (inr dom)
      end).
  End interface.

End AI.


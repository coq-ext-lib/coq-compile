Require Import String List Bool.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Lists.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Data.Map.FMapAList.

Import CpsK.CPSK.

Section AbstractDomain.
  
  Class AbsTime (C : Type) (RD : RelDec (@eq C)) : Type :=
  {
    (** What does this have? 
     ** - there should be a way to refine a context to include some pure fact, e.g.
     **   "assume this equality"
     ** - there should also be a way to record a stack of call sites for context
     **   analysis
     **)
  }.
  
  Class AbsDomain (Domain Value Context ProgramPoint : Type) : Type :=
  { lookup  : Context -> ProgramPoint -> Domain -> Value
  ; update  : Context -> ProgramPoint -> Value -> Domain -> Domain
  ; joinA   : Value -> Value -> Value
  ; bottomA : Value (** this means empty, i.e. never has a value **)
  ; topA    : Value (** this means anything of any type **)
  ; dom_leq   : Domain -> Domain -> bool
  }.

  Class IntValue (V : Type) : Type :=
  { injInt : option BinNums.Z -> V
  ; plusA  : V -> V -> V
  ; minusA : V -> V -> V
  ; timesA : V -> V -> V
  ; eqA    : V -> V -> option bool
  ; ltA    : V -> V -> option bool
  }.

  Class BoolValue (V : Type) : Type :=
  { injBool : option bool -> V
  ; may : V -> bool -> bool
  ; must : V -> bool -> bool
  ; orA : V -> V -> V
  }.

  Class FnValue (V C D : Type) (exp : Type) : Type :=
  { injFn  : C -> list cont -> list var -> exp -> V 
  ; applyA : forall {m} {_ : Monad m}, (C -> D -> exp -> m D%type) -> D -> V -> list V -> list V -> m D%type
  }.

  Class TplValue (V : Type) : Type :=
  { injTuple : list V -> V
  ; projA    : V -> V -> V
  }.

End AbstractDomain.

(** NOTE: This is poorly coded
 ** Don't use a random second monad to be cool
 **)
Section AI.
  Variables D C V : Type.
  Context {Context_dec : RelDec (@eq C)}.
  Context {AbsTime_C  : AbsTime C Context_dec}.
  Context {AbsValue_V : AbsDomain D V C (var + cont)}.
  Context {IntValue_V : IntValue V}.
  Context {BoolValue_V : BoolValue V}.
  Context {FnValue_V  : FnValue V C D exp}.
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

    Definition m' : Type -> Type := 
      readerT C (stateT D m).

    Definition runM' {A} (cmd : m' A) (c : C) (d : D) : m (A * D) :=
      runStateT (runReaderT cmd c) d.
    
    Definition eval_op (o : op) : m' V :=
      match o with
        | Var_o v =>
          domain <- get ;;
          ctx <- ask ;;
          ret (lookup ctx (inl v) domain)
        | Con_o c => ret bottomA (** TODO: Not done **)
        | Int_o i => ret (injInt (Some i))
        | InitWorld_o => ret bottomA (** TODO: ?? **)
      end.
    
    Section Transfer.
      Definition illFormed_decl {A} (d : decl) : m A :=
        raise ("Ill-formed declaration " ++ runShow (show d))%string.
      
      Definition eval_decl (d : decl) : m' unit :=
        v_vA <- 
        match d return m' (var * V) with
          | Op_d v o =>
            oA <- eval_op o ;;
            ret (v, oA)
            
          | Prim_d v p os => 
            argsA <- mapM eval_op os ;;
            vA <- match p , argsA return m' V with
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
                    | _ , _ => lift (lift (illFormed_decl (Prim_d v p os)))
                  end ;;
            ret (v, vA)

          | Fn_d v ks args body =>
            ctx <- ask ;;
            ret (v, injFn ctx ks args body)
            
          | Bind_d v1 v2 m os =>
            ret (v1, topA)
            (*              
            argsA <- mapM eval_op os ;;
            admit
            r <- bindA aeval m argsA ;;
            match r with
              | (a1,a2) =>
                insert v1 a1 ;;
                insert v2 a2
            end
            *)
        end ;;
        let '(v, vA) := v_vA in
        ctx <- ask (T := C) ;;
        modify (update ctx (inl v) vA) ;;
        ret tt.

      Definition init_decl (d : decl) : m' unit :=
        ctx <- ask (T := C) ;;
        match d return m' _ with
          | Op_d v _ 
          | Prim_d v _ _
          | Fn_d v _ _ _ => 
            modify (update ctx (inl v) bottomA)
          | Bind_d v1 v2 _ _ =>
            modify (update ctx (inl v1) bottomA) ;;
            modify (update ctx (inl v2) bottomA)
        end ;;
        ret tt.
      
      Definition aeval : C -> D -> exp -> m D :=
        mfix3 _ (fun aeval => 
          fun (ctx : C) (dom : D) (e : exp) =>
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
                        fA_argsA_d <- runM' (fA <- eval_op o ;;
                          argsA <- mapM eval_op os ;;
                          ret (fA, argsK, argsA)) ctx dom ;;
                        let '((fA, argsK, argsA), dom) := fA_argsA_d in
                          applyA aeval dom fA argsK argsA 
                    | Let_e d e =>
                      v_dom <- runM' (eval_decl d) ctx dom ;;
                      let '(v, dom) := v_dom in
                        recur ctx dom e
                    | AppK_e k os =>
                      fA_argsA_d <- runM' (let fA := lookup ctx (inr k) dom in
                        argsA <- mapM eval_op os ;;
                        ret (fA, argsA)) ctx dom ;;
                      let _ : ((V * list V) * D) := fA_argsA_d in
                        let '((fA, argsA), dom)  := fA_argsA_d in
                          applyA aeval dom fA nil argsA 
                    | LetK_e ks e =>
                      dom' <- runM' 
                      (iterM (fun kxse => let '(k,xs,e) := kxse in
                        modify (update ctx (inr k) (injFn ctx nil xs e)) ;;
                        ret tt) ks) ctx dom ;;
                      recur ctx (snd dom') e
                    | Letrec_e ds e =>
                      dom' <- runM' 
                      (iterM init_decl ds ;;
                        iterM eval_decl ds) ctx dom ;;
                      recur ctx (snd dom') e
                    | Switch_e o arms e =>
                      s <- runM' (eval_op o) ctx dom ;;
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

(*
        Definition aeval : C -> D -> exp -> m D :=
          mfix3 _ (fun aeval => fix recur (ctx : C) (dom : D) (e : exp) : m D :=
            match e return m D with
              | App_e o ks os =>
                let argsK := List.map (fun k => lookup ctx (inr k) dom) ks in
                fA_argsA_d <- runM' (fA <- eval_op o ;;
                                     argsA <- mapM eval_op os ;;
                                     ret (fA, argsK, argsA)) ctx dom ;;
                let '((fA, argsK, argsA), dom) := fA_argsA_d in
                applyA aeval dom fA argsK argsA 
              | Let_e d e =>
                v_dom <- runM' (eval_decl d) ctx dom ;;
                let '(v, dom) := v_dom in
                recur ctx dom e
              | AppK_e k os =>
                fA_argsA_d <- runM' (let fA := lookup ctx (inr k) dom in
                                     argsA <- mapM eval_op os ;;
                                     ret (fA, argsA)) ctx dom ;;
                let _ : ((V * list V) * D) := fA_argsA_d in
                let '((fA, argsA), dom)  := fA_argsA_d in
                applyA aeval dom fA nil argsA 
              | LetK_e ks e =>
                dom' <- runM' 
                  (iterM (fun kxse => let '(k,xs,e) := kxse in
                    modify (update ctx (inr k) (injFn ctx nil xs e)) ;;
                    ret tt) ks) ctx dom ;;
                recur ctx (snd dom') e
              | Letrec_e ds e =>
                dom' <- runM' 
                  (iterM init_decl ds ;;
                   iterM eval_decl ds) ctx dom ;;
                recur ctx (snd dom') e
              | Switch_e o arms e =>
                s <- runM' (eval_op o) ctx dom ;;
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
            end).
*)
    End Transfer.
    
  End Monadic.    

End AI.

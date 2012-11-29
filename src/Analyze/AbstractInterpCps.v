Require Import String.
Require Import CoqCompile.CpsK.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Programming.Show.

Import CpsK.CPSK.

Section AbstractDomain.
  
  Class AbsTime (C : Type) : Type :=
  { (** What does this have? 
     ** - there should be a way to refine a context to include some pure fact, e.g.
     **   "assume this equality"
     **)
  }.
  
  Class AbsDomain (Domain Value Context ProgramPoint : Type) : Type :=
  { lookup  : Context -> ProgramPoint -> Domain -> Value
  ; update  : Context -> ProgramPoint -> Value -> Domain -> Domain
  ; joinA   : Value -> Value -> Value
  ; bottomA : Value (** this means nothing **)
  ; topA    : Value (** this means anything of any type **)
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
  ; applyA : forall {m} {_ : Monad m}, (C -> D -> exp -> m D%type) -> V -> list cont -> list V -> m D%type
  }.

  Class TplValue (V : Type) : Type :=
  { injTuple : list V -> V
  ; projA    : V -> V -> V
  }.

End AbstractDomain.


Section AI.
  Variables D C V : Type.
  Context {AbsTime_C  : AbsTime C}.
  Context {AbsValue_V : AbsDomain D V C (var + cont)}.
  Context {IntValue_V : IntValue V}.
  Context {BoolValue_V : BoolValue V}.
  Context {FnValue_V  : FnValue V C D exp}.
  Context {TplValue_V : TplValue V}.

  Import MonadNotation.
  Local Open Scope monad_scope.
  Local Open Scope list_scope.
  

(*
  Section Maps.
    Variable map_var : Type -> Type.
    Context {FM : DMap Env.var map_var}.
*)
    
    Section Monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {Exc_m : MonadExc string m}.
      Context {Fix_m : MonadFix m}.

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

(**
      Definition insert (v : var) (a : V) : m V :=
        ctx    <- ask ;;
        domain <- get ;;
        let new := joinA (lookup ctx v domain) a in
        put (add v new mp) ;;
        ret new.
**)

      Section Transfer.
        Parameter admit : forall {A}, A.

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
              vA <-
                match p , argsA return m' V with
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
                  | Proj_p , l :: r :: nil => admit
                  | _ , _ => lift (lift (illFormed_decl (Prim_d v p os)))
                end
              ;;
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

        Check @runM'.

        Definition aeval : C -> D -> exp -> m D :=
          mfix3 _ (fun aeval => fix recur (ctx : C) (dom : D) (e : exp) : m D :=
            match e return m D with
              | App_e o ks os =>
                fA_argsA_d <- runM' (fA <- eval_op o ;;
                                     argsA <- mapM eval_op os ;;
                                     ret (fA, argsA)) ctx dom ;;
                let '((fA, argsA), dom) := fA_argsA_d in
                applyA aeval fA ks argsA 
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
                applyA aeval fA nil argsA 
              | LetK_e ks e => admit
              | Letrec_e ds e =>
                dom' <- runM' (iterM eval_decl ds) ctx dom ;;
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

      End Transfer.

(*
      Definition D := ((list decl) * bool)%type. (* fns, escapes *)
      Definition bottomD : D := (nil,false).
      Definition joinD (a b : D) : D :=
        match a , b with
          | (afs,ab),(bfs,bb) => (afs++bfs,orb ab bb)
        end.

      (* structure mostly right...*)
      Definition contApplyA (aeval : exp -> m D) (fn : D) (args : list D) : m D :=
        match fn with
          | (fns,b) =>
            results <- mapM (fun (d:decl) =>
              match d with
                | Fn_d v formals e => 
                  mapM (fun v => match v with
                                   | (f,a) => insert f a
                                 end) (List.combine formals args) ;;
                  aeval e
                | _ => ret bottomD
              end) fns ;;
            ret (fold (fun a b => ret (joinD a b)) (ret bottomD) results)
        end.
        

        Parameter primA : (exp -> m A) -> primop -> list A -> m A.
        Parameter fnA : (exp -> m A) -> decl -> m A.
        Parameter bindA : (exp -> m A) -> mop -> list A -> m (A * A).
*)
    End Monadic.
End AI.


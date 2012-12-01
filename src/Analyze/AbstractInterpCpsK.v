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

Axiom RelDec_exp : RelDec (@eq exp).

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

Module CFA0.

  
  Section Context_aware.
    Variable Context : Type.
    Context {RelDec_c : RelDec (@eq Context)}.
    Context {AbsTime_c : AbsTime Context RelDec_c}.

    Definition AbstractLocation : Type := var.
    Inductive PtValue : Type :=
    | Int : BinNums.Z -> PtValue
(*    | Ptr : AbstractLocation -> PtValue *)
    | Tpl : list Value -> PtValue
    | Clo : Context -> list cont -> list var -> exp -> PtValue
    with Value := 
    | Values : list PtValue -> Value (** use set **)
    | Any    : Value.

    Fixpoint val_leq (v1 v2:Value) : bool :=
      match v1, v2 with
        | Any, Any => true
        | Values vs1, Values vs2 =>
          List.fold_left (fun acc x => 
            match find (fun y => ptval_leq x y) vs2 with
              | None => false
              | Some _ => acc
            end) vs1 true
        | _, Any => true
        | _, _ => false
      end
    with ptval_leq (v1 v2:PtValue) : bool :=
      match v1, v2 with
        | Int _, Int _ => true
        | Tpl vs1, Tpl vs2 => 
          (fix fold_left2 acc ls1 ls2 :=
            match ls1, ls2 with
              | nil, nil => acc
              | x1::ls1, x2::ls2 =>
                if val_leq x1 x2 then acc else false
              | _, _ => false
            end) true vs1 vs2
        | Clo c1 ks1 xs1 e1, Clo c2 ks2 xs2 e2 =>
          rel_dec c1 c2 &&
          rel_dec ks1 ks2 &&
          rel_dec xs1 xs2 &&
          rel_dec e1 e2   
        | _, _ => false
      end.

    Definition Domain : Type := alist (var + cont) Value.
    Definition ProgramPoint : Type := (var + cont)%type.

    Definition bottomValue : Value := Values nil.

    Definition joinValue (v1 v2 : Value) : Value :=
      match v1 , v2 with
        | Any , _ => Any
        | _ , Any => Any
        | Values x , Values y => Values (x ++ y)
      end.

    Global Instance AbsDomain_CFA0 : AbsDomain Domain Value Context ProgramPoint :=
    { lookup  := fun c p d => 
      match Maps.lookup p d with
        | None => bottomValue
        | Some v => v
      end
    ; update  := fun c p v d =>
      match Maps.lookup p d with
        | None => Maps.add p v d
        | Some v_old => Maps.add p (joinValue v_old v) d
      end
    ; joinA   := joinValue
    ; bottomA := bottomValue
    ; topA    := Any
    ; dom_leq   := fun dom1 dom2 => 
      fold_alist (fun k v acc => 
        match Maps.lookup k dom2 with
          | None => false
          | Some v' => val_leq v v'
        end
        ) true dom1
    }.

    Global Instance IntValue_Value : IntValue Value :=
    { injInt := fun v => 
      match v with 
        | None => Any
        | Some v => Values (Int v :: nil)
      end
    ; plusA  := fun x y => Any
    ; minusA := fun x y => Any
    ; timesA := fun x y => Any
    ; eqA    := fun _ _ => None
    ; ltA    := fun _ _ => None
    }.

    Global Instance BoolValue_Value : BoolValue Value :=
    { injBool := fun x => Any
    ; may := fun _ _ => true
    ; must := fun _ _ => false
    ; orA := fun _ _ => Any      
    }.

    Fixpoint list_join_lenAny (ls ls' : list Value) : list Value :=
      match ls , ls' with
        | nil , ls' => ls'
        | ls , nil => ls
        | l :: ls , l' :: ls' =>
          joinA l l' :: list_join_lenAny ls ls'
      end.

    Fixpoint filter_map {A B} (f : A -> option B) (ls : list A) : list B :=
      match ls with
        | nil => nil
        | l :: ls => 
          match f l with
            | None => filter_map f ls
            | Some v => v :: filter_map f ls
          end
      end.

    Definition getNats (ls : list PtValue) : list nat :=
      filter_map (fun x =>
        match x with
          | Int BinNums.Z0 => Some 0
          | Int (BinNums.Zpos n) => Some (BinPos.Pos.to_nat n)
          | _ => None
        end) ls.

    Global Instance TplValue_Value : TplValue Value :=
    { injTuple := fun ls => Values (Tpl ls :: nil)
    ; projA    := fun n t =>
      match t with
        | Any => Any
        | Values vs =>
          let ptwise_tuple := List.fold_left (fun acc x => 
            match x with
              | Tpl vs => list_join_lenAny vs acc
              | _ => acc
            end) vs nil in
          match n with
            | Any => List.fold_left joinA ptwise_tuple bottomA 
            | Values v => 
              let nats := getNats v in
              let all := List.map (fun n => 
                match nth_error ptwise_tuple n with
                  | None => bottomA
                  | Some x => x
                end) nats in
              List.fold_left joinA all bottomA
          end
      end
    }.

    Definition getClos (ls : list PtValue) : list (Context * list cont * list var * exp) :=
      filter_map (fun x =>
        match x with
          | Clo c xs vs e => Some (c, xs, vs, e)
          | _ => None
        end) ls.

    Global Instance FnValue_Value : FnValue Value Context Domain exp :=
    { injFn := fun c ks xs e => Values (Clo c ks xs e :: nil)
    ; applyA := fun _ _ aeval dom v ks vs' =>
      match v with
        | Any => ret dom (** TODO : think more about this! **)
        | Values vs =>
          let clos := getClos vs in
          foldM (fun x acc => let '(c, ks', xs', e) := x in
            if eq_dec (List.length ks') (List.length ks) &&
               eq_dec (List.length xs') (List.length vs) then
              let ext := List.combine (List.map (fun x => inr x) ks') ks 
                      ++ List.combine (List.map (fun x => inl x) xs') vs' in
              let dom' := fold_left (fun acc x => update c (fst x) (snd x) acc) ext dom in 
              aeval c dom' e
            else
              ret acc) (ret dom) clos
      end
    }.

  End Context_aware.

End CFA0.

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
                  | Proj_p , l :: r :: nil => ret (projA l r)
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

Print Assumptions aeval.
(* QED biatch but not really *)
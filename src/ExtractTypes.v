Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Lists.
Require Import String.
Require Import List.
Require Import Strings.

Set Implicit Arguments.
Set Strict Implicit.

Module ExtractTypes.
  Require Import CoqCompile.Lambda.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition type : Type := nat.

  (** Function returns:
   ** 1) map from constructor to arity and type
   ** 2) map of types to constructors 
   **)

  Section using_maps.
    Variable map_ctor : Type -> Type.
    Variable map_type : Type -> Type.
    Context {Map_ctor : DMap Lambda.constructor map_ctor}.
    Context {FMap_ctor : forall x, Reducible (Lambda.constructor * x) (map_ctor x)}.
    Context {Map_type : DMap type map_type}.

    Section monadic.
      Variable m : Type -> Type.
      Variable Monad_m : Monad m.
      Context {State_types : MonadState (map_type (list Lambda.constructor))  m}.
      Context {State_ctors : MonadState (map_ctor (nat * type))  m}.
      Context {State_fresh : MonadState (type) m}.
      Context {Exc_error : MonadExc string m}.

      Definition fresh_type : m type :=
        x <- MonadState.get (MonadState := State_fresh) ;;
        put (S x) ;;
        ret x.

      Definition newCtor (ctor : Lambda.constructor) (arity : nat) : m type :=
        x <- MonadState.get (MonadState := State_ctors) ;;
        match Maps.lookup ctor x with
          | None => 
            t <- fresh_type ;;
            put (Maps.add ctor (arity, t) x) ;;
            y <- MonadState.get (MonadState := State_types) ;;
            put (Maps.add t (ctor :: nil) y) ;;
            ret t
          | Some (arity', t) =>
            if eq_dec arity arity' then
              ret t
            else
              raise ("Found constructor '" ++ ctor ++ "' inconsistent arities: " ++ nat2string10 arity ++ " and " ++ nat2string10 arity')%string
        end.

      Definition mergeTypes' (t1 t2 : type) : m type :=
        map <- MonadState.get (MonadState := State_types) ;;
        match Maps.lookup t1 map with
          | None => ret t2
          | Some ctors => 
            iterM (fun ctor => 
              map' <- MonadState.get (MonadState := State_ctors) ;;
              match Maps.lookup ctor map' with
                | None => raise "type constructor not found"%string
                | Some (arity, t) =>
                  put (Maps.add ctor (arity, t2) map')
              end
              ) ctors ;;
            let map' := Maps.remove t1 map in
            match Maps.lookup t2 map' with
              | None => raise "type constructor not found"%string
              | Some ctors' => 
                put (Maps.add t2 (ctors++ctors') map') ;;
                ret t2
            end
        end.

      Definition mergeTypes (t1 t2 : type) : m type :=
        if eq_dec t1 t2 then ret t1 else mergeTypes' t1 t2.

      Definition newType (ctors : list (Lambda.constructor * nat)) (closed : bool) : m type :=
        ts <- mapM (fun x : Lambda.constructor * nat => newCtor (fst x) (snd x)) ctors ;;
        match ts with
          | nil => fresh_type
          | t::ts => foldM (fun a b => mergeTypes a b) (ret t) ts 
        end.
        
      (** This function will extract types and arity of construcors 
       ** from a Lambda.exp
       **)
      Fixpoint extract' (e : Lambda.exp) : m unit :=
        match e with
          | Lambda.Var_e _ => ret tt
          | Lambda.Lam_e _ e => extract' e
          | Lambda.App_e l r => extract' l ;; extract' r
          | Lambda.Let_e _ l r => extract' l ;; extract' r
          | Lambda.Con_e c ls => 
            mapM extract' ls ;;
            newCtor c (length ls) ;;
            ret tt
          | Lambda.Match_e e arms =>
            extract' e ;;
            mapM (fun x => extract' (snd x)) arms ;;
            let res := 
              List.fold_left (fun acc arm => 
                let '(ctors, closed) := acc in
                  match fst arm with
                    | Lambda.Var_p _ => (ctors, false)
                    | Lambda.Con_p c ls =>
                      ((c, length ls) :: ctors, closed)
                  end) arms (nil, true)
            in
            if eq_dec 0 (length (fst res)) then
              ret tt
            else 
              newType (fst res) (snd res) ;;
              ret tt
          | Lambda.Letrec_e ds b =>
            mapM (fun x => extract' (snd (snd x))) ds ;;
            extract' b
        end.
      End monadic.

      Require Import ExtLib.Data.Monads.EitherMonad.
      Require Import ExtLib.Data.Monads.StateMonad.

      Definition m : Type -> Type :=
        eitherT string (stateT (map_type (list Lambda.constructor)) (stateT (map_ctor (nat * type)) (state type))).

      Definition init_types : map_type (list Lambda.constructor) :=
        Maps.add 0 ("True"::"False"::nil)%string Maps.empty.

      Definition init_ctors : map_ctor (nat * type) :=
        Maps.add "True"%string (0,0) (Maps.add "False"%string (0,0) Maps.empty).

      Definition runM T (cmd : m T) : string + (map_type (list Lambda.constructor) * map_ctor (nat * type)) :=
        let res := (runState (runStateT (runStateT (unEitherT cmd) init_types) init_ctors) 1) in
          match res with
            | (either, mctor, mtyp, _) => 
              match either with
                | inl str => inl str
                | inr _ => inr (mctor, mtyp)
              end
          end.

      Definition extract (e:Lambda.exp) : string + (map_type (list Lambda.constructor) * map_ctor (nat * type)) :=
        runM (@extract' m _ _ _ _ _ e).

    End using_maps.

End ExtractTypes.
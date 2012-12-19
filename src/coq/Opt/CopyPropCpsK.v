Require Import CoqCompile.CpsK CoqCompile.CpsKUtil.
Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Module CopyProp.
  Import MonadNotation CPSK.
  Local Open Scope monad_scope.

  Section with_maps.
    Variable map_v : Type -> Type.
    Context {Map_map_v : DMap var map_v}.

    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {ReaderBindings : MonadReader (map_v op) m}.
    
    Definition copyprop_op (v:op) : m op :=
      match v with
        | Var_o x => 
          x' <- asks (MR := ReaderBindings) (lookup x) ;;
          match x' with
            | Some v => ret v
            | _ => ret v
          end
        | _ => ret v
      end.

    Definition pat2op (p:pattern) : op :=
      match p with
        | Con_p c => Con_o c
        | Int_p i => Int_o i
      end.

    Definition copyprop_k (k : cont) : m cont := ret k.

    (** TODO: Move to library (copied from CloConvK) **)
    Fixpoint filter_map {A B} (f : A -> option B) (ls : list A) : list B :=
      match ls with
        | nil => nil
        | l :: ls => 
          match f l with
            | None => filter_map f ls
            | Some v => v :: filter_map f ls
          end
      end.

    Definition add_all {T} (ls : list (var * op)) : m T -> m T :=
      local (fun acc => fold_left (fun acc x => Maps.add (fst x) (snd x) acc) ls acc).

    Fixpoint copyprop_exp (e:exp) : m exp :=
      match e with
        | AppK_e k vs => 
          vs <- mapM copyprop_op vs ;;
          k <- copyprop_k k ;;
          ret (AppK_e k vs)
        | LetK_e ks e =>
          ks <- mapM (fun k => let '(k,xs,e) := k in
            e <- copyprop_exp e ;;
            ret (k, xs, e)) ks ;;
          e <- copyprop_exp e ;;
          ret (LetK_e ks e)
        | App_e v ks vs => 
          ks <- mapM copyprop_k ks ;;
          vs <- mapM copyprop_op vs ;;
          v <- copyprop_op v ;;
          ret (App_e v ks vs)
        | Let_e d e =>
          copyprop_decl d (fun d => 
            match d with
              | None => copyprop_exp e
              | Some d' => liftM (Let_e d') (copyprop_exp e)
            end)
        | Letrec_e ds e =>
          let copies := filter_map (fun d =>
            match d with
              | Op_d v o => Some (v, o)
              | _ => None
            end) ds in
          add_all copies 
            ((fix go ds (acc : list decl) : m exp :=
              match ds with
                | nil => match acc with
                           | nil => copyprop_exp e
                           | _ =>
                             e <- copyprop_exp e ;;
                             ret (Letrec_e acc e)
                         end
                | d :: ds =>
                  copyprop_decl d (fun od => 
                    go ds match od with
                            | None => acc
                            | Some x => x :: acc
                          end)
              end) ds nil)


        | Switch_e v arms def =>
          v <- copyprop_op v ;;
          arms <- mapM (fun pe => let '(p,e) := pe in
            e <- copyprop_exp e ;;
            ret (p, e)) arms ;;
          def <- match def with
                   | None => ret None
                   | Some d => 
                     d <- copyprop_exp d ;; ret (Some d)
                 end ;;
          ret (Switch_e v arms def)
        | Halt_e o o' => liftM2 Halt_e (copyprop_op o) (copyprop_op o')
      end
    with copyprop_decl {a} (d:decl) (k : option decl -> m a) : m a :=
      match d with
        | Op_d x v => 
          v <- copyprop_op v ;;
          local (add x v) (k None)
        | Prim_d x p vs =>
          vs' <- mapM copyprop_op vs ;;
          let d := Prim_d x p vs' in
          k (Some d)
        | Bind_d x w m vs =>
          vs' <- mapM copyprop_op vs ;;
          k (Some (Bind_d x w m vs))
        | Fn_d f ks xs e =>
          e' <- add_all (map (fun x => (x, Var_o x)) xs) (copyprop_exp e) ;;
          k (Some (Fn_d f ks xs e))
      end.

  End with_maps.

  Require Import ExtLib.Data.Monads.ReaderMonad.
  Require Import ExtLib.Data.Map.FMapAList.
  
  Definition copyprop (e:exp) : exp := 
    runReader (copyprop_exp (map_v := alist var) e) empty.
End CopyProp.

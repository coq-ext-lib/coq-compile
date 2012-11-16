Require Import CoqCompile.Lambda CoqCompile.Cps CoqCompile.CpsUtil.
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

Module Reduce.
  Import MonadNotation CPS.
  Local Open Scope monad_scope.

  Section with_maps.
    Variable map_v : Type -> Type.
    Context {Map_map_v : DMap var map_v}.

    Section monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {ReaderBindings : MonadReader (map_v decl) m}.
    
      Definition reduce_op (v:op) : m op :=
        match v with
          | Var_o x => 
            x' <- asks (MR := ReaderBindings) (lookup x) ;;
            match x' with
              | Some (Op_d _ x) => ret x
              | _ => ret v
            end
          | _ => ret v
        end.
      
      Definition get_tuple (v : op) : m (option (list op)) :=
        match v with 
          | Var_o x =>
            z <- asks (lookup x) ;;
            match z with
              | Some (Prim_d _ MkTuple_p ops) => ret (Some ops)
              | _ => ret None
            end
          | _ => ret None
        end.

      Fixpoint find_arm (v:op) (arms : list (pattern * exp)) (def: option exp)
        : option exp :=
        match v, arms, def with
          | Var_o _, _, _ => None
          | v, nil, x => x
          | Con_o c, ((Int_p _,_)::_), _ => None
          | Int_o i, ((Con_p _,_)::_), _ => None
          | Con_o c, ((Con_p c',e)::arms), def => if eq_dec c c' then Some e else find_arm v arms def
          | Int_o i, ((Int_p i',e)::arms), def => if eq_dec i i' then Some e else find_arm v arms def
        end.

      Definition same_op(v1 v2:op) : m bool :=
        v1 <- reduce_op v1 ;;
        v2 <- reduce_op v2 ;;
        ret match v1, v2 with
              | Int_o i, Int_o j => eq_dec i j
              | Con_o c, Con_o c' => eq_dec c c'
              | Var_o x, Var_o y => eq_dec x y
              | _, _ => false
            end.

      Definition diff_op(v1 v2:op) : m bool :=
        v1 <- reduce_op v1 ;;
        v2 <- reduce_op v2 ;;
        ret match v1, v2 with
              | Int_o i, Int_o j => negb (eq_dec i j)
              | Con_o c, Con_o c' => negb (eq_dec c c')
              | _, _ => false
            end.

      Definition reduce_primop (p:primop) (vs:list op) : m (option op) :=
        match p , vs with
          | Plus_p, (v::(Int_o 0)::nil) => ret (Some v)
          | Plus_p, ((Int_o 0)::v::nil) => ret (Some v)
          | Plus_p, ((Int_o i)::(Int_o j)::nil) => ret (Some (Int_o (i+j)))
          | Minus_p, (v::(Int_o 0)::nil) => ret (Some v)
          | Minus_p, ((Int_o i)::(Int_o j)::nil) => ret (Some (Int_o (i-j)))
          | Times_p, ((Int_o 1)::v::nil) => ret (Some v)
          | Times_p, (v::(Int_o 1)::nil) => ret (Some v)
          | Times_p, ((Int_o i)::(Int_o j)::nil) => ret (Some (Int_o (i*j)))
          | Eq_p, (v1::v2::nil) => 
            same <- same_op v1 v2 ;;
            ret (if same then Some (Con_o "true"%string) else None)
          | Neq_p, (v1::v2::nil) => 
            diff <- diff_op v1 v2 ;;
            ret (if diff then Some (Con_o "true"%string) else None)
          | Lt_p, ((Int_o i)::(Int_o j)::nil) =>
            ret (Some (Con_o (if Z.ltb i j then "true" else "false")%string))
          | Lte_p, ((Int_o i)::(Int_o j)::nil) =>
            ret (Some (Con_o ((if orb (Z.ltb i j) (Z.eqb i j) then "true" else "false")%string)))
          | Ptr_p, ((Con_o _)::nil) => ret (Some (Con_o "false"%string))
          | Ptr_p, ((Var_o x)::nil) =>
            r <- asks (lookup x) ;;
            ret match r with
                  | Some (Prim_d _ MkTuple_p vs) => Some (Con_o "true"%string)
                  | _ => None
                end
          | Proj_p, ((Int_o i)::(Var_o x)::nil) =>
            r <- asks (lookup x) ;;
            ret match r with
                  | Some (Prim_d _ MkTuple_p vs) => nth_error vs (Z.abs_nat i)
                  | _ => None
                end
          | _, _ => ret None
        end.

      Definition pat2op (p:pattern) : op :=
        match p with
          | Con_p c => Con_o c
          | Int_p i => Int_o i
        end.

      Fixpoint reduce_exp (e:exp) : m exp :=
        match e with
          | App_e v k vs => 
            liftM2 (fun x y => App_e x k y) (reduce_op v) (mapM reduce_op vs)
          | AppK_e k vs => 
            liftM (AppK_e k) (mapM reduce_op vs)
          | Let_e d e =>
            reduce_decl d (fun d => 
              match d with
                | None => reduce_exp e
                | Some d' => liftM (Let_e d') (reduce_exp e)
              end)
          | LetK_e ks e =>
            ks <- mapM (fun x => let '(k,xs,e) := x in 
              e <- reduce_exp e ;;
              ret (k,xs,e)) ks ;;
            e <- reduce_exp e ;;
            ret (LetK_e ks e)            
          | Letrec_e ds e =>
            (fix go ds (acc : list decl) : m exp :=
              match ds with
                | nil => match acc with
                           | nil => reduce_exp e
                           | _ =>
                             e <- reduce_exp e ;;
                             ret (Letrec_e acc e)
                         end
                | d :: ds =>
                  reduce_decl d (fun od => 
                    go ds match od with
                            | None => acc
                            | Some x => x :: acc
                          end)
              end
            ) ds nil


          | Switch_e v arms def =>
            v' <- reduce_op v ;; 
            arms' <- mapM (fun p_e => 
              let '(p,e) := p_e in
              e' <- match v' with
                      | Var_o x => 
                        let o := Op_d x (pat2op p) in
                        local (add x o) (reduce_exp e)
                      | _ => reduce_exp e
                    end ;;
              ret (p, e')) arms ;;
            def' <- mapM reduce_exp def ;;
            match find_arm v' arms' def' with
              | None => ret (switch_e v' arms' def')
              | Some e => ret e
            end 
          | Halt_e o => liftM Halt_e (reduce_op o)
        end
      with reduce_decl {a} (d:decl) (k : option decl -> m a) : m a :=
        match d with
          | Op_d x v => 
            v <- reduce_op v ;;
            local (add x (Op_d x v)) (k None)
          | Prim_d x p vs =>
            vs' <- mapM reduce_op vs ;;
            p' <- reduce_primop p vs' ;;
            match p' with
              | None => let d := Prim_d x p vs' in
                local (add x d) (k (Some d))
              | Some v => 
                local (add x (Op_d x v)) (k None)
            end
          | Bind_d x w m vs =>
            vs' <- mapM reduce_op vs ;;
            k (Some (Bind_d x w m vs))
          | Fn_d f k' xs e =>
            e' <- reduce_exp e ;;
              match match_etas xs e with
                | None => k (Some (Fn_d f k' xs e))
                | Some v => local (add f (Op_d f v)) (k None)
              end
        end.
    End monadic.

    Require Import ExtLib.Data.Monads.ReaderMonad.
    
    Definition reduce (e:exp) : exp := 
      runReader (reduce_exp e) empty.
  End with_maps.
End Reduce.

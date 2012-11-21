Require Import CoqCompile.Cps.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.

Import Cps.CPS.

Section AI.
  Import MonadNotation.
  Local Open Scope monad_scope.
  Local Open Scope list_scope.
  
  Parameter A : Type.
  Parameter join : A -> A -> A.
  Parameter bottom : A.

  Section Maps.
    Variable map_var : Type -> Type.
    Context {FM : DMap Env.var map_var}.
    
    Section Monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {State_m : MonadState (map_var A) m}.
      Context {Fix_m : MonadFix m}.
      
      Definition inj (o : op) : m A :=
        match o with
          | Var_o v =>
            inMap <- gets (lookup v) ;;
            match inMap with
              | None => ret bottom
              | Some a => ret a
            end
          | _ => ret bottom
        end.
      
      Definition insert (v : var) (a : A) : m A :=
        map <- get ;;
        let new := match lookup (map:=map_var) v map with
                     | Some o => join o a
                     | None => a
                   end
        in put (add v new map) ;;
        ret new.

      Section Transfer.
        Parameter applyA : (exp -> m A) -> A -> list A -> m A.
        Parameter primA : (exp -> m A) -> primop -> list A -> m A.
        Parameter fnA : (exp -> m A) -> decl -> m A.
        Parameter bindA : (exp -> m A) -> mop -> list A -> m (A * A).
        
        Definition deval (aeval : exp -> m A) (d : decl) : m A :=
          match d with
            | Op_d v o =>
              a <- inj o ;;
              insert v a
            | Prim_d v p os => 
              argsA <- mapM inj os ;;
              a <- primA aeval p argsA ;;
              insert v a
            | Fn_d v _ _ =>
              a <- fnA aeval d ;;
              insert v a
            | Bind_d v1 v2 m os =>
              argsA <- mapM inj os ;;
              r <- bindA aeval m argsA ;;
              match r with
                | (a1,a2) =>
                  insert v1 a1 ;;
                  insert v2 a2
              end
          end.
        
        Definition aeval : exp -> m A :=
          mfix (fun aeval => fix recur (e : exp) : m A := 
            match e with
              | App_e o os =>
                fA <- inj o ;
                argsA <- mapM inj os ;;
                applyA aeval fA argsA
              | Let_e d e =>
                deval aeval d ;;
                aeval e
              | Letrec_e ds e =>
                mapM (deval aeval) ds ;;
                aeval e
              | Switch_e o arms e =>
                s <- inj o ;;
                armsR <- mapM (fun x => aeval (snd x)) arms ;;
                armsA <- foldM (fun a b => ret (join a b)) (ret bottom) armsR ;;
                match e with
                  | Some e =>
                    default <- aeval e ;;
                    ret (join armsA default)
                  | None =>
                    ret armsA
                end
              | Halt_e o1 o2 =>
                inj o1
            end).

      End Transfer.

      Definition D := ((list decl) * bool)%type. (* fns, escapes *)
      Definition bottomD : D := (nil,false).
      Definition joinD (a b : D) : D :=
        match a , b with
          | (afs,ab),(bfs,bb) => (afs++bfs,orb ab bb)
        end.

      (* structure mostly right... &#$@%@$ monads and sections *)
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
    End Monadic.
  End Maps.
End AI.


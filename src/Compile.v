Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Map.FMapAList.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.ExtLib.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Programming.Show.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.Cps CoqCompile.CpsK.
Require Import CoqCompile.LLVM.
Require Import CoqCompile.CodeGen CoqCompile.CloConvK.
Require Import CoqCompile.ExtractTypes.
Require Import CoqCompile.Parse.
Require Import CoqCompile.TraceMonad.

Set Implicit Arguments.
Set Strict Implicit.

Module Compile.
  Section maps.
    Variable map_ctor : Type -> Type.
    Context {FM : DMap Lambda.constructor map_ctor}.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Section monadic.
      Variable m : Type -> Type.
      Variable Monad_m : Monad m.
      Context {State_fresh : MonadState Z m}.
      Context {Exc_error : MonadExc string m}.
      
      Definition next : m Z :=
        l <- get (MonadState := State_fresh) ;;
        put (MonadState := State_fresh) (l+1)%Z ;;
        ret ((l*2)+1)%Z.

      Definition makeCtorMap' (e:Lambda.exp) : m (map_ctor Z) :=
        match ExtractTypes.extract e with
          | inl str => raise str
          | inr (mtype, mctor) =>
            foldM (m := m) (fun k_v acc =>
              let '(k,v) := k_v in
              foldM (fun ctor acc =>
                match Maps.lookup ctor mctor with
                  | None => raise "constructor not found"%string 
                  | Some (arity, _) =>
                    n <- (if string_dec "True" ctor
                           then ret 3
                           else if string_dec "False" ctor
                                  then ret 1
                                  else next)%Z ;;
                    let map' := Maps.add ctor n acc in
                    ret map'
                end
              ) (ret acc) v
            ) (ret Maps.empty) mtype
        end.
      
    End monadic.

  End maps.


  Module Opt.
    Require Import CoqCompile.Optimize.
    Require CoqCompile.Opt.CseCpsK.
    Require CoqCompile.Opt.DeadCodeCpsK.

    Section monadic.
      Variable m : Type -> Type.
      Context {Monad_m : Monad m}.
      Context {MonadExc_m : MonadExc string m}.
      Context {MoandTrace_m : MonadTrace string m}.

      Definition optimization e : Type := Optimize.optimization e m.

      Definition O0 : optimization CPSK.exp := fun x => ret x.
      Definition O1 : optimization CPSK.exp := fun x => 
        ret (CseCpsK.Cse.cse (DeadCodeCpsK.dce x)).

      Definition runOpt {E} (o : optimization E) (e : E) : m E := o e.
    End monadic.
  End Opt.

    (* Definition m : Type -> Type := *)
    (*   stateT Z (sum string). *)

    (* Definition runM (cmd:m (map_ctor Z)) : string + map_ctor Z := *)
    (*   let res := evalStateT cmd 2%Z in *)
    (*   match res with *)
    (*     | inl str => inl str *)
    (*     | inr mctor => inr mctor *)
    (*   end. *)

  Section Driver.
    Require CoqCompile.CpsKConvert.
    Require CoqCompile.CpsK2Low.

    Import MonadNotation.
    Local Open Scope monad_scope.
    Import ShowNotation.

    Definition m : Type -> Type :=
      eitherT string (traceT string ident).

    Definition runM {A} (c : m A) : (string + A) * list string :=
      unIdent (traceTraceT (unEitherT c)).

    Definition makeCtorMap (e:Lambda.exp) : m (alist Lambda.constructor Z) :=
      evalStateT (@makeCtorMap' (alist Lambda.constructor) _ (stateT _ m) _ _ _ e) 2%Z.

    Variable word_size : nat.
    Variable cps_opt :  @Opt.optimization m CPSK.exp.

    Definition phase {T U} {S : Show U} (name : string) 
      (c : U -> m T) (x : U)
      : m T :=
      catch (c x) 
            (fun (err : string) => 
              let err : string := 
                runShow (name << ": "%string << err 
                         << Char.chr_newline << to_string x)%show
              in raise err).

    Global Instance Show_lam : Show Lambda.exp :=
    { show := fun x => "todo"%string }.

    Definition topCompile (io : bool) (e:Lambda.exp) : m LLVM.module :=
      mctor <- makeCtorMap e ;;
      cps_e <- phase "CpsConvert"%string 
        (match io return Lambda.exp -> m CPSK.exp with
           | true => fun x => ret (CpsKConvert.CPS_io x)
           | false => fun x => ret (CpsKConvert.CPS_pure x)
         end) e ;;
      let _ : CPSK.exp := cps_e in
      opt_e <- phase "Optimize"%string cps_opt cps_e ;;
      let _ : CPSK.exp := opt_e in
      clo_conv_e <- phase "Closure Convert"%string (@CloConvK.ClosureConvert.cloconv_exp _ _ _) cps_e ;;
      low <- phase "Low" (S := fun x => show (CPSK.Letrec_e (fst x) (snd x))) (fun x => CoqCompile.CpsK2Low.cpsk2low _ (fst x) (snd x)) clo_conv_e ;;
      phase "Codegen" (CodeGen.generateProgram word_size mctor) low.

    Definition topCompile_string (io : bool) (e : Lambda.exp) : (string + string) :=
      match unIdent (traceTraceT (unEitherT (topCompile io e))) with
        | (inl e, t) => inl (e ++ to_string t)%string
        | (inr mod', t) => inr (runShow (show mod') ""%string)
      end.
    
    Definition stringToCPS (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          CpsK.CPSK.exp2string (CpsKConvert.CPS_pure e)
      end.

    Definition stringToClos (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure e)) with
            | inl e => e
            | inr (ds,e) => to_string (CPSK.Letrec_e ds e)
          end
      end.

    Definition stringToLow (s : string) : string :=
       match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure e)) with
            | inl e => e
            | inr (decls,main) =>
              match (CpsK2Low.cpsk2low _ decls main) with
                | inl e => e
                | inr low => to_string low
              end
          end
      end.
(*
    Definition stringToAssembly (s: string) : string + string :=
      match Parse.parse_topdecls s with
        | None => inl "Failed to parse."%string
        | Some e =>
          match topCompile e with
            | inl s => inl s
            | inr module => inr (runShow (show module) ""%string)
          end
      end.
*)

    Definition topCompileFromStr (io : bool) (e:string) : (string + string) :=
      match Parse.parse_topdecls e with
        | None => inl "Failed to parse."%string
        | Some e => topCompile_string io e
      end.
  End Driver.

End Compile.

Module CompileTest.
  Import Lambda.
  Import LambdaNotation.

  Definition identity : string := "(define ident (lambda (x) ident))"%string.

  Definition e_ident : Lambda.exp :=
    Eval compute in 
      match Parse.parse_topdecls identity with
        | None => Lambda.Var_e (Env.wrapVar ""%string)
        | Some o => o
      end.

  Definition fact :=
  "(define plus (lambdas (n m)
     (match n
       ((O) m)
       ((S p) `(S ,(@ plus p m))))))
  
   (define mult (lambdas (n m)
     (match n
       ((O) `(O))
       ((S p) (@ plus m (@ mult p m))))))
  
   (define fact (lambda (n)
     (match n
       ((O) `(S ,`(O)))
       ((S n~) (@ mult n (fact n~))))))"%string.

  Definition e_fact : Lambda.exp :=
    Eval vm_compute in 
      match Parse.parse_topdecls fact with
        | None => Lambda.Var_e (Env.wrapVar ""%string)
        | Some o => o
      end.

  Eval vm_compute in
    Compile.stringToCPS fact.

  Eval vm_compute in
    Compile.stringToClos fact.

  Eval vm_compute in
    Compile.stringToLow fact.

  Eval vm_compute in
    match Compile.runM (Compile.topCompile 8 (@Compile.Opt.O0 Compile.m _) false e_fact) with
      | (inl err, t) => (err, t)
      | (inr mod', t) => (to_string mod', t)
    end.

End CompileTest.

Require Import ZArith String List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
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

    Definition m : Type -> Type :=
      stateT Z (sum string).

    Definition runM (cmd:m (map_ctor Z)) : string + map_ctor Z :=
      let res := evalStateT cmd 2%Z in
      match res with
        | inl str => inl str
        | inr mctor => inr mctor
      end.

    Definition makeCtorMap (e:Lambda.exp) : string + map_ctor Z :=
      runM (@makeCtorMap' m _ _ _ e).

  End maps.


  Module Opt.
    Require Import CoqCompile.Optimize.
    Require CoqCompile.Opt.CseCps.
    Require CoqCompile.Opt.DeadCodeCpsK.

    Definition optimization e : Type := Optimize.optimization e (sum string).

    Definition O0 : optimization CPSK.exp := fun x => ret x.
    Definition O1 : optimization CPSK.exp := fun x => ret (DeadCodeCpsK.dce x).

    Definition runOpt {E} (o : optimization E) (e : E) : string + E := o e.
  End Opt.

  Section Driver.
    Require CoqCompile.CpsKConvert.
    Require CoqCompile.CpsK2Low.

    Import MonadNotation.
    Local Open Scope monad_scope.
    Import ShowNotation.

    
    Variable word_size : nat.
    Variable cps_opt :  Opt.optimization CPSK.exp.

    Definition phase {T U} {S : Show U} (name : string) 
      (c : U -> string + T) (x : U)
      : string + T :=
      catch (c x) 
            (fun (err : string) => 
              let err : string := 
                runShow (name << ": "%string << err 
                         << Char.chr_newline << to_string x)%show
              in raise err).

    Definition topCompile (io : bool) (e:Lambda.exp) : string + LLVM.module :=
      mctor <- makeCtorMap e ;;
      let cps_e := 
        if io then CpsKConvert.CPS_io e else CpsKConvert.CPS_pure e 
      in
      opt_e <- phase "Optimize"%string cps_opt cps_e ;;
      clo_conv_e <- phase "Closure Convert"%string CloConvK.ClosureConvert.cloconv_exp cps_e ;;
      low <- phase "Low" (S := fun x => show (CPSK.Letrec_e (fst x) (snd x))) (fun x => CoqCompile.CpsK2Low.cpsk2low _ (fst x) (snd x)) clo_conv_e ;;
      phase "CodeGen" (CodeGen.generateProgram word_size mctor) low.

    Definition topCompile_string (e : Lambda.exp) : string + string := 
      match topCompile true e with
        | inl e => inl e
        | inr mod' => inr (runShow (show mod') ""%string)
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
    match Compile.topCompile 8 Compile.Opt.O0 false (e_fact) with
      | inl err => err
      | inr mod' => to_string mod'
    end.

(*  Eval vm_compute in
    match Compile.topCompile 8 Compile.Opt.O0 false (gen e3) with
      | inl err => err
      | inr mod' =>  to_string mod'
    end.*)

End CompileTest.

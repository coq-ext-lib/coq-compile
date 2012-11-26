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

    Definition optimization : Type := Optimize.optimization CPS.exp (sum string).
    Definition optimizationK : Type := Optimize.optimization CPSK.exp (sum string).

    Definition O0 : optimization := fun x => ret x.
    Definition O1 : optimization := 
      fun x => ret (CseCps.Cse.cse x).

    Definition runOpt (o : optimization) (e : CPS.exp) := o e.
  End Opt.

  Section Driver.
    Require CoqCompile.CpsKConvert.
    Require CoqCompile.CpsK2Low.

    Import MonadNotation.
    Local Open Scope monad_scope.
    
    Variable word_size : nat.
    Variable cps_opt :  Opt.optimizationK.

    Definition topCompile (io : bool) (e:Lambda.exp) : string + LLVM.module :=
      mctor <- makeCtorMap e ;;
      let cps_e := 
        if io then CpsKConvert.CPS_io e else CpsKConvert.CPS_pure e 
      in
      opt_e <- cps_opt cps_e ;;
      clo_conv_e <- CloConvK.ClosureConvert.cloconv_exp opt_e ;;
      low <- CoqCompile.CpsK2Low.cpsk2low _ (fst clo_conv_e) (snd clo_conv_e) ;;
      CodeGen.generateProgram word_size mctor low.

    Definition topCompile_string (e : Lambda.exp) : string + string := 
      match topCompile true e with
        | inl e => inl e
        | inr mod' => inr (runShow (show mod') ""%string)
      end.
    
    Definition stringToCPS (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          CpsK.CPSK.exp2string (CpsKConvert.CPS_io e)
      end.

(*
    Definition stringToClos (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          CpsK.CPSK.exp2string (CloConv.ClosureConvert.cloconv_exp (CpsConvert.CPS_io e))
      end.

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

(*
Module CompileTest.
  Import Lambda.
  Import LambdaNotation.

  Definition blah (e:Lambda.exp) :=
      let cps_e := CpsConvert.CPS e in
      let clo_conv_e := CloConv.ClosureConvert.cloconv_exp cps_e in
      (cps_e, clo_conv_e).

  Definition e_ident : Lambda.exp :=
    Eval compute in 
      match Parse.parse_topdecls "(define ident (lambda (x) x))"%string with
        | None => Lambda.Var_e (Env.wrapVar ""%string)
        | Some o => o
      end.

  Eval vm_compute in (blah e_ident).

  Eval vm_compute in    
    match Compile.topCompile 8 Compile.Opt.O0 (gen e3) with
      | inl err => err
      | inr mod' => runShow (show mod') ""%string
    end.

End CompileTest.
*)
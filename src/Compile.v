Require Import Lambda Cps.
Require Import ZArith String List Bool.
Require Import ExtLib.Monad.Monad.
Require Import ExtLib.Monad.OptionMonad ExtLib.Monad.StateMonad.
Require Import ExtLib.Monad.Folds.
Require Import ExtLib.Monad.EitherMonad.
Require Import ExtLib.Data.Strings.
Require Import ExtLib.Decidables.Decidable.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.FMaps.FMaps.
Require Import LLVM.
Require Import CodeGen.
Require Import CloConv.
Require Import ExtractTypes.
Require Import Parse.

Set Implicit Arguments.
Set Strict Implicit.

Module Compile.
  Section maps.
    Variable map_ctor : Type -> Type.
    Context {FM : Map CPS.var map_ctor}.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Section monadic.
      Variable m : Type -> Type.
      Variable Monad_m : Monad m.
      Context {State_fresh : State Z m}.
      Context {Exc_error : MonadExc string m}.
      
      Definition next : m Z :=
        l <- get (State := State_fresh) ;;
        put (State := State_fresh) (l+1)%Z ;;
        ret ((l*2)+1)%Z.

      Definition makeCtorMap' (e:Lambda.exp) : m (map_ctor Z) :=
        match ExtractTypes.ExtractTypes.extract e with
          | inl str => raise str
          | inr (mtype, mctor) =>
            fmap_foldM (fun k v acc =>
              foldM (fun ctor acc =>
                match FMaps.lookup ctor mctor with
                  | None => raise "constructor not found"%string 
                  | Some (arity, _) =>
                    n <- (if string_dec "True" ctor
                           then ret 1
                           else if string_dec "False" ctor
                                  then ret 3
                                  else next)%Z ;;
                    let map' := FMaps.add ctor n acc in
                    ret map'
                end
              ) acc v
            ) (FMaps.empty) mtype
        end.
      
    End monadic.

    Definition m : Type -> Type :=
      eitherT string (state Z).

    Definition runM (cmd:m (map_ctor Z)) : string + map_ctor Z :=
      let res := (runState (unEitherT cmd) 2%Z) in
        match res with
          | (either, _) =>
            match either with
              | inl str => inl str
              | inr mctor => inr mctor
            end
        end.

    Definition makeCtorMap (e:Lambda.exp) : string + map_ctor Z :=
      runM (@makeCtorMap' m _ _ _ e).

  End maps.


  Module Opt.
    Require CoqCompile.Opt.CseCps.

    Definition optimizer : Type := CPS.exp -> CPS.exp.

    Definition ident : optimizer := fun x => x.

    Fixpoint chain (opts : list optimizer) : optimizer :=
      match opts with
        | nil => ident
        | opt :: opts =>
          let r := chain opts in
          fun x => r (opt x)
      end.

    Fixpoint iterate (n : nat) (opt : optimizer) : optimizer :=
      match n with
        | 0 => ident
        | 1 => opt
        | S n => fun x => opt (iterate n opt x)
      end.

    Definition O0 : optimizer := ident.
    Definition O1 : optimizer := 
      CseCps.Cse.cse.
  End Opt.


  Section Driver.
    
    Variable word_size : nat.
    Variable cps_opt : Opt.optimizer.

    Definition topCompile (e:Lambda.exp) : string + LLVM.module :=
      let m := makeCtorMap e in
      let cps_e := Cps.CPS.CPS e in
      let clo_conv_e := CloConv.ClosureConvert.cloconv_exp cps_e in
      let opt_cc_e := cps_opt clo_conv_e in
      match m with
        | inl str => inl str
        | inr mctor => CodeGen.CodeGen.toModule word_size mctor (opt_cc_e)
      end.

    Definition topCompile_string (e : Lambda.exp) : string + string := 
      match topCompile e with
        | inl e => inl e
        | inr mod' => inr (LLVM.string_of_module mod' ""%string)
      end.
    
    Definition stringToCPS (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          Cps.CPS.exp2string (Cps.CPS.CPS e)
      end.

    Definition stringToClos (s : string) : string :=
      match Parse.parse_topdecls s with
        | None => "Failed to parse."%string
        | Some e =>
          Cps.CPS.exp2string (CloConv.ClosureConvert.cloconv_exp (Cps.CPS.CPS e))
      end.

    Definition stringToAssembly (s: string) : string + string :=
      match Parse.parse_topdecls s with
        | None => inl "Failed to parse."%string
        | Some e =>
          match topCompile e with
            | inl s => inl s
            | inr module => inr (LLVM.string_of_module module "")
          end
      end.

  End Driver.

End Compile.

Module CompileTest.
  Import Lambda.
  Import LambdaNotation.

  Definition blah (e:Lambda.exp) :=
      let cps_e := Cps.CPS.CPS e in
      let clo_conv_e := CloConv.ClosureConvert.cloconv_exp cps_e in
      (cps_e, clo_conv_e).

  Definition e_ident : Lambda.exp :=
    Eval compute in 
      match Parse.parse_topdecls "(define ident (lambda (x) x))"%string with
        | None => Lambda.Var_e ""%string
        | Some o => o
      end.

  Eval vm_compute in (blah e_ident).

  Eval vm_compute in    
    match Compile.topCompile 8 Compile.Opt.O0 (gen e3) with
      | inl err => err
      | inr mod' => (LLVM.string_of_module mod' ""%string)
    end.

End CompileTest.
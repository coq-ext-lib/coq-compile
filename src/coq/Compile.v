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
                                  else if string_dec "Tt" ctor
                                         then ret 3
                                         else next)%Z ;;
                    let map' := Maps.add ctor n acc in
                    ret map'
                end
              ) (ret acc) v
            ) (ret Maps.empty) mtype
        end.
      
    End monadic.

  End maps.

  Definition m : Type -> Type :=
    eitherT string (traceT string ident).

  Definition runM {A} (c : m A) : (string + A) * list string :=
    unIdent (traceTraceT (unEitherT c)).


  Module Opt.
    Require Import CoqCompile.Optimize.
    Require CoqCompile.Opt.CseCpsK.
    Require CoqCompile.Opt.DeadCodeCpsK.
    Require CoqCompile.Opt.ReduceCpsK.

    Definition optimization e : Type := Optimize.optimization e m.
    
    Definition O0 : optimization CPSK.exp := fun x => ret x.
    Definition O1 : optimization CPSK.exp := fun x => 
      ret (CseCpsK.Cse.cse (DeadCodeCpsK.dce x)).
    Definition O2 : optimization CPSK.exp := fun x =>
      ret (ReduceCpsK.Reduce.reduce (CseCpsK.Cse.cse (DeadCodeCpsK.dce x))).
    
    Definition runOpt {E} (o : optimization E) (e : E) : m E := o e.
  End Opt.

  Section Driver.
    Require CoqCompile.CpsKConvert.
    Require CoqCompile.CpsK2Low.
    Require Import CoqCompile.Analyze.Reachability.

    Import MonadNotation.
    Local Open Scope monad_scope.
    Import ShowNotation.

    Definition makeCtorMap (e:Lambda.exp) : m (alist Lambda.constructor Z) :=
      evalStateT (@makeCtorMap' (alist Lambda.constructor) _ (stateT _ m) _ _ _ e) 2%Z.

    Variable word_size : nat.
    Variable cps_opt :  @Opt.optimization CPSK.exp.

    Record Phase (T U : Type) : Type :=
    { Phase_Show : Show T
    ; name : string 
    ; run : T -> m U
    }.

    Global Instance Show_lam : Show Lambda.exp :=
    { show := fun x => "todo"%string }.

    Definition Phase_CpsConvert (io : bool) : Phase Lambda.exp CPSK.exp :=
    {| Phase_Show := _
     ; name := "CpsConvert"
     ; run := fun x =>
       if io then
         ret (CpsKConvert.CPS_io x)
       else 
         ret (CpsKConvert.CPS_pure x)
     |}.

    Definition Phase_Opt (o : Opt.optimization CPSK.exp) : Phase CPSK.exp CPSK.exp :=
    {| Phase_Show := _
     ; name := "Optimize"
     ; run := fun x => Opt.runOpt o x
     |}.

    Definition Phase_CloConv : Phase CPSK.exp (list CPSK.decl * CPSK.exp) :=
    {| Phase_Show := _
     ; name := "Closure Convert" 
     ; run := fun x =>
       CloConvK.ClosureConvert.cloconv_exp x
     |}.

    Definition Phase_OptCc : Phase (list CPSK.decl * CPSK.exp) (list CPSK.decl * CPSK.exp) :=
    {| Phase_Show := _
     ; name := "Optimize Closure Convert"
     ; run := fun x => let '(ds,m) := x in
       ret (ds, m) (** TODO **)
     |}.


    Definition Phase_Lower (dupdate : bool) : Phase (list CPSK.decl * CPSK.exp) Low.program :=
     {| Phase_Show := fun x => show (CPSK.Letrec_e (fst x) (snd x))
      ; name := "Lower"
      ; run := fun x =>
        liveMap <- (if dupdate then
                      construct_live_map _ (CPSK.Letrec_e (fst x) (snd x)) 100
                    else ret None) ;;
        CoqCompile.CpsK2Low.cpsk2low_h _ liveMap (fst x) (snd x)
      |}.

    Definition Phase_LLVM (mctor : _) : Phase Low.program LLVM.module :=
    {| Phase_Show := _
     ; name := "Code Gen"
     ; run := fun x =>
       CodeGen.generateProgram word_size mctor x
     |}.

    Definition phase {T U} {S : Show U} (name : string) 
      (c : U -> m T) (x : U)
      : m T :=
      catch (c x) 
            (fun (err : string) => 
              let err : string := 
                runShow (name << ": "%string << err 
                         << Char.chr_newline << to_string x)%show
              in raise err).

    Definition phase_bind {A B} (p : Phase A B) : A -> m B := 
      phase (S := Phase_Show p) (name p) (run p).

    Inductive CompileTo : Type :=
    | Lam_stop
    | Cps_stop
    | OptCps_stop
    | Clo_stop
    | OptClo_stop
    | Low_stop
    | LLVM_stop.

    Local Notation "p1 >>= p2" := (bind p1 (phase_bind p2)).

    Definition topCompile (io : bool) (e:Lambda.exp) (stop_at : CompileTo) (dupdate : bool) 
      : m match stop_at with
            | Lam_stop => Lambda.exp
            | LLVM_stop => LLVM.module
            | Low_stop => Low.program
            | Clo_stop => list CPSK.decl * CPSK.exp
            | OptClo_stop => list CPSK.decl * CPSK.exp
            | _ => CPSK.exp
          end :=
      mctor <- makeCtorMap e ;;
      match stop_at as stop_at 
        return m match stop_at with
                   | Lam_stop => Lambda.exp
                   | LLVM_stop => LLVM.module
                   | Low_stop => Low.program
                   | Clo_stop => list CPSK.decl * CPSK.exp
                   | OptClo_stop => list CPSK.decl * CPSK.exp
                   | _ => CPSK.exp
                 end with
        | Lam_stop => ret e
        | Cps_stop => (ret e) >>= (Phase_CpsConvert io)
        | OptCps_stop => (ret e) >>= (Phase_CpsConvert io) >>= (Phase_Opt cps_opt)
        | Clo_stop => (ret e) >>= (Phase_CpsConvert io) >>= (Phase_Opt cps_opt) >>= (Phase_CloConv)
        | OptClo_stop => (ret e) >>= (Phase_CpsConvert io) >>= (Phase_Opt cps_opt) >>= (Phase_CloConv) >>= (Phase_OptCc)
        | Low_stop =>  (ret e) >>= (Phase_CpsConvert io) >>= (Phase_Opt cps_opt) >>= (Phase_CloConv) >>= (Phase_OptCc) >>= (Phase_Lower dupdate)
        | LLVM_stop =>
          (ret e) >>= (Phase_CpsConvert io) >>= (Phase_Opt cps_opt) >>= (Phase_CloConv) >>= (Phase_OptCc) >>= (Phase_Lower dupdate) >>= (Phase_LLVM mctor)
      end.

    (** Test Hooks **)
    Definition topCompile_string (io : bool) (e : Lambda.exp) (stop_at : CompileTo) (dupdate : bool) : string + string :=
      match unIdent (traceTraceT (unEitherT (topCompile io e stop_at dupdate))) with
        | (inl e, t) => inl (e ++ to_string t)%string
        | (inr mod', t) => 
          let str := 
            match stop_at as stop_at
              return match stop_at with
                       | Lam_stop => Lambda.exp
                       | LLVM_stop => LLVM.module
                       | Low_stop => Low.program
                       | Clo_stop => list CPSK.decl * CPSK.exp
                       | OptClo_stop => list CPSK.decl * CPSK.exp
                       | _ => CPSK.exp
                     end -> string
              with
              | Lam_stop => to_string
              | LLVM_stop => to_string
              | Low_stop => to_string
              | Clo_stop
              | OptClo_stop => fun x => to_string (CPSK.Letrec_e (fst x) (snd x))
              | _ => to_string
            end
          in
          inr (str mod')
      end.
    
    Definition stringToCPS (s : string) : string :=
      match Parse.parse_topdecls s with
        | inl e => e
        | inr e =>
          CpsK.CPSK.exp2string (CpsKConvert.CPS_pure e)
      end.

    Definition stringToClos (s : string) : string :=
      match Parse.parse_topdecls s with
        | inl e => e
        | inr e =>
          match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure e)) with
            | inl e => e
            | inr (ds,e) => to_string (CPSK.Letrec_e ds e)
          end
      end.

    Definition stringToLow (s : string) : string :=
       match Parse.parse_topdecls s with
        | inl e => e
        | inr e =>
          match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure e)) with
            | inl e => e
            | inr (decls,main) =>
              match traceTraceT ((CpsK2Low.cpsk2low _ decls main)) with
                | inl e => e
                | inr low => String Char.chr_newline (to_string low)
              end
          end
      end.

    Definition lamToCPS (l : Lambda.exp) : string :=
      String Char.chr_newline (to_string (CpsKConvert.CPS_pure l)).

    Definition lamToClos (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure l)) with
        | inl e => e
        | inr (ds,e) => String Char.chr_newline (to_string (CPSK.Letrec_e ds e))
      end.

    Definition lamToLow (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure l)) with
        | inl e => e
        | inr (decls,main) =>
          match traceTraceT ((CpsK2Low.cpsk2low _ decls main)) with
            | inl e => e
            | inr low => String Char.chr_newline (to_string low)
          end
      end.

    Definition lamToCPSIO (l : Lambda.exp) : string :=
      String Char.chr_newline (to_string (CpsKConvert.CPS_io l)).

    Definition lamToClosIO (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_io l)) with
        | inl e => e
        | inr (ds,e) => String Char.chr_newline (to_string (CPSK.Letrec_e ds e))
      end.

    Definition lamToLowIO (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_io l)) with
        | inl e => e
        | inr (decls,main) =>
          match traceTraceT ((CpsK2Low.cpsk2low _ decls main)) with
            | inl e => e
            | inr low => String Char.chr_newline (to_string low)
          end
      end.

    Definition topCompileFromStr (io : bool) (e:string) (stop : CompileTo) (dupdate : bool) : string + string :=
      parse <- Parse.parse_topdecls e ;;
      topCompile_string io parse stop dupdate.

  End Driver.

End Compile.

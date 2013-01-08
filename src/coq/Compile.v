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
(* Require Import CoqCompile.Optimize. *)
Require CoqCompile.Opt.CseCpsK.
Require CoqCompile.Opt.DeadCodeCpsK.
Require CoqCompile.Opt.ReduceCpsK.
Require CoqCompile.Opt.AlphaCvtCpsK.
Require CoqCompile.Opt.CopyPropCpsK.

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
            let init := (
              Maps.add "StdOut" 1 (
              Maps.add "StdErr" 3 (
              Maps.add "Tt" 3 (
              Maps.add "False" 1 (
              Maps.add "True" 3 (
              Maps.empty))))))%Z
            in
            foldM (m := m) (fun k_v acc =>
              let '(k,v) := k_v in
              foldM (fun ctor acc =>
                match Maps.lookup ctor acc with
                  | Some _ => ret acc
                  | None => 
                    match Maps.lookup ctor mctor with
                      | None => raise "constructor not found"%string 
                      | Some (arity, _) =>
                        n <- next ;;
                        let map' := Maps.add ctor n acc in
                        ret map'
                    end
                end
              ) (ret acc) v
            ) (ret init) mtype
        end%string.
      
    End monadic.

  End maps.

  Section Driver.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MonadExc_m : MonadExc string m}.
    Context {MonadTrace_m : MonadTrace string m}.

    Definition optimization e : Type := e -> m e.
    
    Definition O0 : optimization CPSK.exp := fun x => ret x.
    Definition O1 : optimization CPSK.exp := fun x => 
      let alpha := AlphaCvtCpsK.AlphaCvt.alpha_cvt x in
        ret (CopyPropCpsK.CopyProp.copyprop (CseCpsK.Cse.cse (DeadCodeCpsK.dce alpha))).
    Definition O2 : optimization CPSK.exp := fun x =>
      let alpha := AlphaCvtCpsK.AlphaCvt.alpha_cvt x in
        ret (CopyPropCpsK.CopyProp.copyprop (ReduceCpsK.Reduce.reduce (CseCpsK.Cse.cse (DeadCodeCpsK.dce alpha)))).
  
    Definition runOpt {E} (o : optimization E) (e : E) : m E := o e.

    Require CoqCompile.CpsKConvert.
    Require CoqCompile.CpsK2Low.
    Require Import CoqCompile.Analyze.Reachability.

    Import MonadNotation.
    Local Open Scope monad_scope.
    Import ShowNotation.

    Definition makeCtorMap (e:Lambda.exp) : m (alist Lambda.constructor Z) :=
      evalStateT (@makeCtorMap' (alist Lambda.constructor) _ (stateT _ m) _ _ _ e) 2%Z.

    Variable word_size : nat.
    Variable cps_opt :  optimization CPSK.exp.

    Inductive IR : Type :=
    | IR_Raw
    | IR_Lam
    | IR_Cps
    | IR_Clo
    | IR_Low
    | IR_LLVM.

    Definition denoteIR (ir : IR) : Type :=
      match ir with
        | IR_Raw => string
        | IR_Lam => Lambda.exp
        | IR_Cps => CPSK.exp
        | IR_Clo => CPSK.cc_program
        | IR_Low => Low.program
        | IR_LLVM => LLVM.module
      end%type.

    Global Instance Show_denoteIR ir : Show (denoteIR ir) :=
    { show :=
      match ir as ir return denoteIR ir -> showM with
        | IR_Raw => show_exact
        | IR_Lam => show
        | IR_Cps => show
        | IR_Clo => show
        | IR_Low => show
        | IR_LLVM => show
      end }.

    Record Phase (T U : IR) : Type :=
    { name : string 
    ; run : denoteIR T -> m (denoteIR U)
    }.

    Definition Phase_CpsConvert (io : bool) : Phase IR_Lam IR_Cps :=
    {| name := "CpsConvert"
     ; run := fun x : denoteIR IR_Lam =>
       match io return m (denoteIR IR_Cps) with
         | true =>
           ret (CpsKConvert.CPS_io x)
         | false =>
           ret (CpsKConvert.CPS_pure x)
       end
     |}.

    Definition Phase_Opt (o : optimization CPSK.exp) : Phase IR_Cps IR_Cps :=
    {| name := "Optimize"
     ; run := fun x : denoteIR IR_Cps => runOpt o x : m (denoteIR IR_Cps)
     |}.

    Definition Phase_CloConv : Phase IR_Cps IR_Clo :=
    {| name := "Closure Convert" 
     ; run := fun x : denoteIR IR_Cps =>
       CloConvK.ClosureConvert.cloconv_exp x : m (denoteIR IR_Clo)
     |}.

    Definition Phase_OptCc : Phase IR_Clo IR_Clo :=
    {| name := "Optimize Closure Convert"
     ; run := fun x : denoteIR IR_Clo =>
       ret (DeadCodeCpsK.dce_cc x : denoteIR IR_Clo)
     |}.

    Definition Phase_Lower (dupdate : bool) : Phase IR_Clo IR_Low :=
     {| name := "Lower"
      ; run := fun x : denoteIR IR_Clo =>
        liveMap <- (if dupdate then
                      construct_live_map _ (CPSK.Letrec_e x.(CPSK.decls) x.(CPSK.main)) 100
                    else ret None) ;;
        CoqCompile.CpsK2Low.cpsk2low_h _ liveMap x.(CPSK.decls) x.(CPSK.main)
          : m (denoteIR IR_Low)
      |}.

    Definition Phase_LLVM (mctor : _) : Phase IR_Low IR_LLVM :=
    {| name := "Code Gen"
     ; run := fun x : denoteIR IR_Low =>
       CodeGen.generateProgram word_size mctor x : m (denoteIR IR_LLVM)
     |}.

    Definition Phase_Sane : Phase IR_Cps IR_Cps :=
    {| name := "Sane"
     ; run := fun x : denoteIR IR_Cps =>
       catch (CpsK.CPSK.exp_sane x ;; ret x)
             (fun err : string => raise err)
    |}.

    Require Import ExtLib.Data.Monads.FuelMonad.
    Require CpsKSemantics.

    Definition Phase_Check (fuel : N) : Phase IR_Cps IR_Cps :=
    {| name := "Check"
     ; run := fun x : denoteIR IR_Cps =>
       let c := CpsKSemantics.eval_exp nil x in
       match runStateT (runStateT (runGFixT c fuel) nil) nil with
         | inl err => raise err
         | inr (None, _ ,_) => mlog "out of fuel"%string ;; ret x
         | inr (Some v, _, _) => mlog ("returned " ++ to_string v)%string ;; ret x
       end
     |}.

    Definition Phase_Debug (p : Phase IR_Cps IR_Cps) : Phase IR_Cps IR_Cps :=
    {| name := "Debug:" ++ name p
     ; run := fun x : denoteIR IR_Cps =>
       let go x := 
         runStateT (runStateT (runGFixT (CpsKSemantics.eval_exp nil x) 10000) nil) nil in
       y <- run p x ;;
       match go x , go y with
         | inl l , inl r => raise "preserved error"%string
         | inr (Some _, _, _) , inl err =>
           raise (runShow ("introduced error: " << err << Char.chr_newline << 
                             "before ------------------" << Char.chr_newline <<
                             show x << Char.chr_newline <<
                             "after ------------------" << Char.chr_newline <<
                             show y))%string%show
         | inl _ , inr _ => raise "masked error"%string
         | inr _ , inr _ => ret y
         | inr (None,_,_) , inl _ => ret y
       end           
     |}.

    Definition getPhase (name : string) (ir : IR) : option { ir' : IR & Phase ir ir' } :=
      (** TODO: This should fill in a way to get different phases
       ** It is currently stubbed because the naive way to do it will generate an enormous
       ** amount of code...
       **)
      None.

    Definition phase {T U} {S : Show U} (name : string) 
      (c : U -> m T) (x : U)
      : m T :=
      catch (mlog ("Phase Start: " ++ name)%string ;;
             res <- c x ;;
             mlog ("Phase End: " ++ name)%string ;;
             ret res) 
            (fun (err : string) => 
              let err : string := 
                runShow (name << ": "%string << err 
                         << Char.chr_newline << to_string x)%show
              in raise err).

    Definition phase_bind {A B} (p : Phase A B) : denoteIR A -> m (denoteIR B) := 
      phase (name p) (run p).

    Inductive CompileTo : Type :=
    | Lam_stop
    | Cps_stop
    | OptCps_stop
    | Clo_stop
    | OptClo_stop
    | Low_stop
    | LLVM_stop.

    Definition denoteCompileTo (stop : CompileTo) : Type :=
      match stop with
        | Lam_stop => Lambda.exp
        | LLVM_stop => LLVM.module
        | Low_stop => Low.program
        | Clo_stop => CPSK.cc_program
        | OptClo_stop => CPSK.cc_program
        | _ => CPSK.exp
      end.

    Global Instance Show_denoteCompileTo ir : Show (denoteCompileTo ir) :=
    { show :=
      match ir as ir return denoteCompileTo ir -> showM with
        | Lam_stop => show
        | Cps_stop => show
        | OptCps_stop => show
        | Clo_stop => show
        | OptClo_stop => show
        | Low_stop => show
        | LLVM_stop => show
      end }.

    Local Notation "p1 >>= p2" := (bind p1 (phase_bind p2)).

    Definition topCompile (io : bool) (e:Lambda.exp) (stop_at : CompileTo) (dupdate : bool) 
      : m match stop_at with
            | Lam_stop => Lambda.exp
            | LLVM_stop => LLVM.module
            | Low_stop => Low.program
            | Clo_stop => CPSK.cc_program
            | OptClo_stop => CPSK.cc_program
            | _ => CPSK.exp
          end :=
      mctor <- makeCtorMap e ;;
      match stop_at as stop_at 
        return m match stop_at with
                   | Lam_stop => Lambda.exp
                   | LLVM_stop => LLVM.module
                   | Low_stop => Low.program
                   | Clo_stop => CPSK.cc_program
                   | OptClo_stop => CPSK.cc_program
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
  End Driver.

  Section Testing.
    Definition m : Type -> Type :=
      eitherT string (traceT string ident).

    Definition runM {A} (c : m A) : (string + A) * list string :=
      unIdent (traceTraceT (unEitherT c)).

    Variable word_size : nat.
    Variable cps_opt :  optimization m CPSK.exp.

    (** Test Hooks **)
    Definition topCompile_string (io : bool) (e : Lambda.exp) (stop_at : CompileTo) (dupdate : bool) : string + string :=
      match unIdent (traceTraceT (unEitherT (topCompile word_size cps_opt io e stop_at dupdate))) with
        | (inl e, t) => inl (e ++ to_string t)%string
        | (inr mod', t) => 
          let str := 
            match stop_at as stop_at
              return match stop_at with
                       | Lam_stop => Lambda.exp
                       | LLVM_stop => LLVM.module
                       | Low_stop => Low.program
                       | Clo_stop => CPSK.cc_program
                       | OptClo_stop => CPSK.cc_program
                       | _ => CPSK.exp
                     end -> string
              with
              | Lam_stop => to_string
              | LLVM_stop => to_string
              | Low_stop => to_string
              | Clo_stop
              | OptClo_stop => to_string
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
            | inr ccp => to_string ccp
          end
      end.

    Definition stringToLow (s : string) : string :=
       match Parse.parse_topdecls s with
        | inl e => e
        | inr e =>
          match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure e)) with
            | inl e => e
            | inr ccp =>
              match traceTraceT ((CpsK2Low.cpsk2low _ ccp.(CPSK.decls) ccp.(CPSK.main))) with
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
        | inr ccp => String Char.chr_newline (to_string ccp)
      end.

    Definition lamToLow (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_pure l)) with
        | inl e => e
        | inr ccp =>
          match traceTraceT ((CpsK2Low.cpsk2low _ ccp.(CPSK.decls) ccp.(CPSK.main))) with
            | inl e => e
            | inr low => String Char.chr_newline (to_string low)
          end
      end.

    Definition lamToCPSIO (l : Lambda.exp) : string :=
      String Char.chr_newline (to_string (CpsKConvert.CPS_io l)).

    Definition lamToClosIO (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_io l)) with
        | inl e => e
        | inr ccp => String Char.chr_newline (to_string ccp)
      end.

    Definition lamToLowIO (l : Lambda.exp) : string :=
      match (CloConvK.ClosureConvert.cloconv_exp (CpsKConvert.CPS_io l)) with
        | inl e => e
        | inr ccp =>
          match traceTraceT ((CpsK2Low.cpsk2low _ ccp.(CPSK.decls) ccp.(CPSK.main))) with
            | inl e => e
            | inr low => String Char.chr_newline (to_string low)
          end
      end.
  End Testing.

End Compile.

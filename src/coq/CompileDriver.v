Require Import String.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Programming.Show.
Require Import CoqCompile.Lambda.
Require Import CoqCompile.Compile.
Require CoqCompile.Parse.
Require Import CoqCompile.TraceMonad.
Require CoqIO.IO.

Set Implicit Arguments.
Set Strict Implicit.

Import ShowNotation.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope show_scope.

Definition m (T : Type) : Type := IO.IO (string + T).

Instance Monad_m : Monad.Monad m :=
{| bind := fun _ x _ f =>
   IO.IO_bind _ x _ (fun x => match x with 
                                | inl x => IO.IO_ret _ (inl x)
                                | inr x => f x
                              end)
 ; ret := fun _ x => IO.IO_ret _ (inr x)
 |}.

Instance Trace_IO : MonadTrace string m :=
{ mlog := fun msg : string => 
  bind (runShow (M := IO.ShowScheme_Std IO.StdErr) (show_exact msg << Char.chr_newline))%show
       (fun x => ret (inr x))
}.

Instance Exc_IO : MonadExc string m :=
{ raise := fun _ x => IO.IO_ret _ (inl x)
; catch := fun _ c h =>
  IO.IO_bind _ c _ (fun x => 
    match x with
      | inl err => h err
      | inr x => ret x
    end)
}.

Definition printLine (s : IO.std) (msg : showM) : IO.IO unit :=
  runShow (M := IO.ShowScheme_Std s) (msg << Char.chr_newline)%show.

Section parametric.
  Variables (word_size : nat) (opt : Compile.optimization m CpsK.CPSK.exp) (with_io : bool) 
    (stop : Compile.CompileTo) (destructive_update : bool) (out : Ascii.ascii -> IO.IO unit).

  Definition compile_lam (e : Lambda.exp) : IO.IO bool :=
    r_or_err <- (@Compile.topCompile m _ _ _ word_size opt with_io e stop destructive_update : IO.IO (string + _)) ;;
    match r_or_err with
      | inl err => 
        printLine IO.StdErr err ;;
        ret false
      | inr res =>
        runShow (M := IO.ShowScheme_IO out) (show res  << Char.chr_newline) ;;
        ret true
    end.


  Definition compile_string (prg : string) : IO.IO bool :=
    match Parse.Parse.parse_topdecls prg with
      | inl err =>
        printLine IO.StdErr err ;;
        ret false
      | inr e =>
        printLine IO.StdErr "Done parsing"%string ;;
        compile_lam e
    end.
End parametric.

Definition opt0 := @Compile.O0 m _.
Definition opt1 := @Compile.O1 m _.
Definition opt2 := @Compile.O2 m _.
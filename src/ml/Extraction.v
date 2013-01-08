Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import String.
Extraction Blacklist String List.
Require CoqIO.IO.

(** Since we're going to extract to Ocaml, we need to set up different
 ** extractions for the IO primitives
 **)
Extract Constant IO.IO "'t" => " 't CoqIO.io ".
Extract Inductive IO.std => "CoqIO.std" [ "CoqIO.StdOut" "CoqIO.StdErr" ].
Extract Inlined Constant IO.IO_bind => "CoqIO.io_bind".
Extract Inlined Constant IO.IO_ret => "CoqIO.io_ret".
Extract Inlined Constant IO.IO_printChar => "CoqIO.io_printChar".
Extract Inlined Constant IO.IO_printCharF => "CoqIO.io_printCharF".
Extract Inlined Constant IO.IO_read => "CoqIO.io_read".
Extraction Language Ocaml.

(* We'll use Extraction to one monolithic file. *)
Require Import CoqCompile.Compile.

Require Import CoqCompile.TraceMonad.
Require Import ExtLib.Programming.Show.

Definition m (T : Type) : Type := IO.IO (string + T).
Require Import ExtLib.Structures.Monads.
Instance Monad_m : Monad.Monad m :=
{| bind := fun _ x _ f =>
   IO.IO_bind _ x _ (fun x => match x with 
                                | inl x => IO.IO_ret _ (inl x)
                                | inr x => f x
                              end)
 ; ret := fun _ x => IO.IO_ret _ (inr x)
 |}.
Import ShowNotation.
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

Require CoqCompile.Parse.
Definition topcompile : 
  nat -> Compile.optimization m CpsK.CPSK.exp -> bool -> string ->
  Compile.CompileTo -> bool -> (Ascii.ascii -> IO.IO unit) -> IO.IO bool :=
  fun ws o b e c b' out =>
    match Parse.Parse.parse_topdecls e with
      | inl err =>
        IO.IO_bind _ (runShow (M := IO.ShowScheme_Std IO.StdErr) (show_exact err)) _ (fun _ => IO.IO_ret _ false)
      | inr e =>
        let res := @Compile.topCompile m _ _ _ ws o b e c b' in
        IO.IO_bind _ res _ 
          (fun r_or_err => 
            match r_or_err with
              | inl err => IO.IO_bind _ (runShow (M := IO.ShowScheme_Std IO.StdErr) (show_exact err)) _ (fun _ => IO.IO_ret _ false)
              | inr res => IO.IO_bind _ (runShow (M := IO.ShowScheme_IO out) (show res)) _ (fun _ => IO.IO_ret _ true)
            end)
    end.

Definition opt0 := @Compile.O0 m _.
Definition opt1 := @Compile.O1 m _.
Definition opt2 := @Compile.O2 m _.

Time Extraction "CoqCompile.ml" topcompile opt0 opt1 opt2.

Require Import CoqCompile.CpsKSemantics.
Definition topeval := evalstr.
Time Extraction "CoqCpsKSemantics.ml" topeval val2str.

(* Just for testing purposes. *)
(*
Require Parse.
Extraction "extraction/Compile.ml" Parse.Parse.parse_topdecls.
*)

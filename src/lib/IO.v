Require Ascii.

Parameter IO : Type -> Type.

Parameter IO_bind : forall a, IO a -> forall b, (a -> IO b) -> IO b.
Parameter IO_ret  : forall a, a -> IO a.
Parameter IO_printChar : Ascii.ascii -> IO unit.

(** Other IO **)
Inductive std : Type := StdOut | StdErr.
Parameter IO_printCharF : std -> Ascii.ascii -> IO unit.
Parameter IO_read : IO Ascii.ascii.

(** Instances **)
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Programming.Show.

Global Instance Monad_IO : Monad IO :=
{ bind := IO_bind
; ret  := IO_ret
}.

Definition ShowScheme_IO (f : Ascii.ascii -> IO unit) : ShowScheme (IO unit) :=
{| show_inj := f
 ; show_mon := {| Monoid.monoid_plus := fun x y => bind x (fun _ => y)
                ; Monoid.monoid_unit := ret tt
                |}
 |}.

Definition ShowScheme_Std (f : std) : ShowScheme (IO unit) :=
  ShowScheme_IO (IO_printCharF f).


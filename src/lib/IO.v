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

Definition ShowScheme_IO (f : std) : ShowScheme (IO unit) :=
{| show_inj := IO_printCharF f
 ; show_mon := {| Monoid.monoid_plus := fun x y => bind x (fun _ => y)
                ; Monoid.monoid_unit := ret tt
                |}
 |}.

(** Extraction Hints **)
Extract Constant IO "t" => "t".
Extract Constant IO_bind => "io_bind".
Extract Constant IO_ret => "io_ret".
Extract Constant IO_printChar => "io_printChar".
Extract Constant IO_printCharF => "io_printCharF".
Extract Constant IO_read => "io_read".
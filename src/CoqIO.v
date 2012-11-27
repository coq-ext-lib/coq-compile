Require Import ZArith.

(* Signature for IO operations *)

Parameter IO : Type -> Type.
Parameter IO_ret : forall {T:Type}, T -> IO T.
Parameter IO_bind : forall {T U:Type}, IO T -> (T -> IO U) -> IO U.
Parameter IO_printint : forall {T:Type}, T -> IO unit.

Extract Constant IO "T" => "IO T".
Extract Constant IO_ret => "IO_ret".
Extract Constant IO_bind => "IO_bind".
Extract Constant IO_printint => "IO_printint".

Definition blah := IO_ret 5.
Definition blah2 := IO_printint (5%positive).

Set Extraction Language Scheme.

Recursive Extraction blah2.
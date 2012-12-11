Definition ident (x: nat) := x.

Definition call_ident :=
  let x := 0 in
  let y := 1 in
  let z := ident x in
  (y,z).
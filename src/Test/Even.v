Fixpoint even (n:nat) : bool :=
  match n with
    | O => true
    | S n => odd n
  end
with odd (n:nat) : bool :=
  match n with
    | O => false
    | S n => even n
  end.

Definition true := even 200.
Definition false := even 201.

Definition gc_test :=
  let a := even 20 in
  let b := even 21 in
  let c := even 22 in
  let d := even 23 in
  andb a (andb b (andb c d)).
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
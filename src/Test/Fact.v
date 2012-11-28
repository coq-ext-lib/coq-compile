Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => n * fact n'
  end.
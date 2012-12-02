Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => n * fact n'
  end.

Definition fact6 := fact 6.

Fixpoint tr_fact' (acc : nat) (n : nat) : nat :=
  match n with
    | O => acc
    | S n' =>
      let acc := n * acc in
      tr_fact' acc n'
  end.

Definition tr_fact (n : nat) := tr_fact' 1 n.

Definition tr_fact6 := tr_fact 6.
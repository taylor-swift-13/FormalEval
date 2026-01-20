
Require Import ZArith.

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => O
  | S O => 1
  | S (S O) => 1
  | S (S (S k)) => fib (S k) + fib (S (S k))
  end.

Definition fib_spec (n : nat) (result : nat) : Prop :=
  result = fib n.


Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S m) => fib (S m) + fib m
  end.

Definition fib_spec (n : Z) (res : Z) : Prop :=
  res = fib (Z.to_nat n).

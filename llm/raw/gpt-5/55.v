Require Import Coq.ZArith.ZArith.

Fixpoint fibn (n : nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S n') => fibn (S n') + fibn n'
  end.

Definition fib_spec (n : Z) (res : Z) : Prop :=
  (0 <= n /\ res = Z.of_nat (fibn (Z.to_nat n))) \/
  (n < 0 /\ res = 1%Z).
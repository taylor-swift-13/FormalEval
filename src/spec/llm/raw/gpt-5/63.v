
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.

Fixpoint fibfib_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | S (S (S k)) => fibfib_nat (S (S k)) + fibfib_nat (S k) + fibfib_nat k
  end.

Definition fibfib_spec (n : Z) (res : Z) : Prop :=
  0 <= n /\ res = Z.of_nat (fibfib_nat (Z.to_nat n)).

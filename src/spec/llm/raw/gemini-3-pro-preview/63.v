
Require Import Coq.Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | S (S (S p)) => fibfib (S (S p)) + fibfib (S p) + fibfib p
  end.

Definition fibfib_spec (n : nat) (result : nat) : Prop :=
  result = fibfib n.

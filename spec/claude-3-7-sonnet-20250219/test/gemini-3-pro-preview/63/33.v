Require Import Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | S p => fibfib p + fibfib (pred p) + fibfib (pred (pred p))
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 17 5768.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.
Require Import Arith Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output : nat) : Prop :=
  2 * output = n * (n + 1).

Example problem_60_test_case:
  problem_60_spec 2 3.
Proof.
  unfold problem_60_spec.
  simpl.
  lia.
Qed.
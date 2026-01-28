Require Import ZArith.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output : nat) : Prop :=
  2 * output = n * (n + 1).

Example test_case_1 : problem_60_spec 999 499500.
Proof.
  unfold problem_60_spec.
  lia.
Qed.
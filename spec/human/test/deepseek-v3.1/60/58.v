Require Import ZArith.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output : nat) : Prop :=
  2 * output = n * (n + 1).

Example test_case_new : problem_60_spec 85 3655.
Proof.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.
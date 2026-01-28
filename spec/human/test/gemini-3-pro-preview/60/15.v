Require Import Coq.Arith.Arith.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 1000 -> problem_60_spec 1000 500500.
Proof.
  intros H.
  unfold problem_60_spec.
  reflexivity.
Qed.
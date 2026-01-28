Require Import Coq.Arith.Arith.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 12 -> problem_60_spec 12 78.
Proof.
  intros H.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.
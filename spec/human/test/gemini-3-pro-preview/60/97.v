Require Import Coq.Arith.Arith.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 95 -> problem_60_spec 95 4560.
Proof.
  intros H.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.
Require Import Arith.

Definition problem_41_spec (input output : nat) : Prop :=
  output = input * input.

Example test_case_9999 : problem_41_spec 9999 99980001.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.
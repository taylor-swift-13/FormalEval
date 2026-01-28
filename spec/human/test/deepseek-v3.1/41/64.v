Require Import Arith.

Definition problem_41_spec (input output : nat) : Prop :=
  output = input * input.

Example test_example : problem_41_spec 58 3364.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.
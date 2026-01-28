Require Import Arith.

Definition problem_41_spec (input output : nat) : Prop :=
  output = input * input.

Example test_example : problem_41_spec 987654 975460423716.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.
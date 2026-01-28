Require Import Arith.

Definition problem_41_spec (input output : nat) : Prop :=
  output = input * input.

Example test_example : problem_41_spec 987652 975456473104.
Proof.
  unfold problem_41_spec.
  compute.
  reflexivity.
Qed.
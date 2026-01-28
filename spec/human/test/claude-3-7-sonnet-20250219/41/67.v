Require Import Arith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 998 996004.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.
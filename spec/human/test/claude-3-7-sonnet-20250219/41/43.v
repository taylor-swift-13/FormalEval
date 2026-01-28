Require Import Nat.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_test_case :
  problem_41_spec 1000 1000000.
Proof.
  reflexivity.
Qed.
Require Import ZArith.

Open Scope Z_scope.

Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec (input output : Z) : Prop :=
  output = input * input.

Example problem_41_test_case :
  problem_41_spec 1000000000 1000000000000000000.
Proof.
  unfold problem_41_spec.
  reflexivity.
Qed.
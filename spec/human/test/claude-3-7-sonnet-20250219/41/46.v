Require Import ZArith.

Open Scope Z_scope.

Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 9999 99980001.
Proof.
  unfold problem_41_spec.
  simpl.
  reflexivity.
Qed.
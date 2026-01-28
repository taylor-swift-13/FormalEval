Require Import Arith.
Require Import ZArith.
Open Scope Z_scope.

Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec (input output : Z) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 987653 975458448409.
Proof.
  simpl.
  reflexivity.
Qed.
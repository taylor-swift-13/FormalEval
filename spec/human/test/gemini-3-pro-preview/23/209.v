Require Import String.
Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "    This is a sample TTetnstrinisg to test the function           " 66.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.
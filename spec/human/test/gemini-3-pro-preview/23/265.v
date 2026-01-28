Require Import String.
Open Scope string_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_2: problem_23_spec "Tis          " 13.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.
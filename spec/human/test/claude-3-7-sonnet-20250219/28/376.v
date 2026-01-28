Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_numeric_string_list :
  problem_28_spec ["1234567890"] "1234567890".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
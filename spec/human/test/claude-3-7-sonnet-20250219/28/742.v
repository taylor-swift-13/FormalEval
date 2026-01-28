Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_multiple_strings :
  problem_28_spec ["123"; "456"; "1amuchb0"; "789"; "10"; "11"; "12"; "14"; "16"; "117"; "18"] "1234561amuchb0789101112141611718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
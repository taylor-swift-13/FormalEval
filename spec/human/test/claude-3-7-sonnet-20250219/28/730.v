Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_non_empty_string_list :
  problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "15"; "16"; "17"; "18"] "12345678910111215161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
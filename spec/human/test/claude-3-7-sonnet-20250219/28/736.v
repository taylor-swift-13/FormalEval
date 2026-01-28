Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_long_strings :
  problem_28_spec ["456"; "789"; "10"; "11"; "12"; "13"; "17"; "18"; "11"; "123!amuchb"; "11"; "123!amuchb"] "45678910111213171811123!amuchb11123!amuchb".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
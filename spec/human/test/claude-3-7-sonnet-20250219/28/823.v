Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_no_789_10_11_extra123_12_14_15_16_empty_3113_18 :
  problem_28_spec ["no"; "789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "no7891011extra12312141516311318".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
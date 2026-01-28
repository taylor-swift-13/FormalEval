Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_mixed_strings :
  problem_28_spec ["789"; "10"; "11"; "extra123"; "12"; "14"; "15"; "16"; ""; "3113"; "18"] "7891011extra12312141516311318".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_string_list :
  problem_28_spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"] "123no78910111213141516thealazy31131811".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
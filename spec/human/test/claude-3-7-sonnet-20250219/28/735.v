Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_long_list :
  problem_28_spec ["123"; "456"; "789"; "10"; "11"; "12"; "spaces"; "13"; "14"; "15"; "16"; "17"; "18"; "15"; "10"] "123456789101112spaces1314151617181510".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
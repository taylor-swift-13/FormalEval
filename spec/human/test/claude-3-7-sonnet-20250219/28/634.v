Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_string_list :
  problem_28_spec ["123"; "456"; "10"; "11"; "12"; "13"; "14"; "15"; "1"; "17"; "14"] "12345610111213141511714".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
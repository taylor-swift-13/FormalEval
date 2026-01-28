Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concatenate_multiple_strings :
  problem_28_spec ["1123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "17"; "18"] "1123456789🦌1112131415161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
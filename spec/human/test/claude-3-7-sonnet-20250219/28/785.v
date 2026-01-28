Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_long_strings :
  problem_28_spec ["123"; "45"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "or"; "18"; "123"] "1234578910111214151617or18123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
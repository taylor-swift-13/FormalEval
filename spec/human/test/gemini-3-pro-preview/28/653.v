Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "15"; "16"; "without"; "18"; "13"; "12"] "123456789🦌111213141516without181312".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
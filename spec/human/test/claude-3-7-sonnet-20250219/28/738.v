Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_non_empty_string_list :
  problem_28_spec ["123"; "6"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "18"; "11"; "10"] "1236111213141516lazy181110".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
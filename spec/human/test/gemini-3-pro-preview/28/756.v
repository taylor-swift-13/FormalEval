Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "6"; "10"; "11"; "12"; "13"; "14"; "15"; "lazy"; "18"; "11"; "10"] "1236101112131415lazy181110".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
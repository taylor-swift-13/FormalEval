Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "45"; "789"; "10"; "11"; "12"; "14"; "15"; "16"; "17"; "18"; "123"] "123457891011121415161718123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
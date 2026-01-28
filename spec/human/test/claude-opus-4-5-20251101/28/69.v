Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_two_strings :
  problem_28_spec ["123"; "456"] "123456".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
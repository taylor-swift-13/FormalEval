Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_empty_string : problem_28_spec [] "".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
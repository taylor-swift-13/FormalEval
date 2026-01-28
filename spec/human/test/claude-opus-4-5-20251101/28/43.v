Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_multiple :
  problem_28_spec ["orana45e6ge"; "apple"; "banana"; "orange"] "orana45e6geapplebananaorange".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
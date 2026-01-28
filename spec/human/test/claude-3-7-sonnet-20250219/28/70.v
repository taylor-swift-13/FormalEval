Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_world_banana_orange :
  problem_28_spec ["world"; "banana"; "orange"] "worldbananaorange".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
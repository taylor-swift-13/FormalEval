Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_oran456ge_banana_orangeoran456ge :
  problem_28_spec ["oran456ge"; "banana"; "orangeoran456ge"] "oran456gebananaorangeoran456ge".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
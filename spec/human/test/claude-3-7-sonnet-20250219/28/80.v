Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_oran456ge_apple_banana_orange_orange :
  problem_28_spec ["oran456ge"; "apple"; "banana"; "orange"; "orange"] "oran456geapplebananaorangeorange".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
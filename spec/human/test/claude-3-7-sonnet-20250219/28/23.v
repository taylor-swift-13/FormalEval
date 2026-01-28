Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_apple_i456banana_orange_apple :
  problem_28_spec ["apple"; "i456banana"; "orange"; "apple"] "applei456bananaorangeapple".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
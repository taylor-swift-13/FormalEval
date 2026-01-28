Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "2"%string; "4"%string; "5"%string; "6"%string; "66"%string; "7"%string; "8"%string; "9"%string; "5"%string] ("12456667895"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
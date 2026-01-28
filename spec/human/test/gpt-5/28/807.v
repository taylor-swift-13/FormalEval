Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "🦁"%string; "10"%string; "🐼"%string; "🐨"%string; "🐯"%string; "🦛"%string; "🦢"%string; "12"%string; "🦜"%string; "🐢"%string; "🐻"%string] ("🐻🦁10🐼🐨🐯🦛🦢12🦜🐢🐻"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
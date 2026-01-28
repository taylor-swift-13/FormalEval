Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "🦁"%string; "🦊"%string; "🐼t!!shis
string
has
multiple
newlines"%string; "🐨"%string; "🐯"%string; "🦛"%string; "🦌"%string; "🦢"%string; "🦜"%string; "🐢"%string; "🦊"%string] ("🐻🦁🦊🐼t!!shis
string
has
multiple
newlines🐨🐯🦛🦌🦢🦜🐢🦊"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
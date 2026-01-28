Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🦁"%string; "🦉Hw"%string; "How"%string; "🦊"%string; "🐨"%string; "🦛"%string; "🦌"%string; "multipule"%string; "🦉"%string; "🦜"%string; "🐢"%string; "🦉"%string; "🦌"%string] ("🦁🦉HwHow🦊🐨🦛🦌multipule🦉🦜🐢🦉🦌"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
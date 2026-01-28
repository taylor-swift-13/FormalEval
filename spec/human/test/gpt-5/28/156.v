Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["😀"%string; "🌞"%string; "this"%string; "🧐"%string; "spac13s"%string; "★1"%string; "★"%string] ("😀🌞this🧐spac13s★1★"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
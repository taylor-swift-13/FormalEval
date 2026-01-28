Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "456"%string; "8789"%string; "10"%string; "11"%string; "12"%string; "1614"%string; "🦛"%string; "14"%string; "15"%string; "16"%string; "lazy"%string; "313"%string; "18"%string; "11"%string] ("12345687891011121614🦛141516lazy3131811"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
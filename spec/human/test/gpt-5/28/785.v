Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "45"%string; "789"%string; "10"%string; "11"%string; "12"%string; "14"%string; "15"%string; "16"%string; "17"%string; "or"%string; "18"%string; "123"%string] ("1234578910111214151617or18123"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
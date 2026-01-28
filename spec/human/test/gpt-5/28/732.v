Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["456"%string; "789"%string; "10"%string; "11"%string; "12"%string; "13"%string; "17"%string; "18"%string; "11"%string; "123!amuchb"%string; "11"%string] ("45678910111213171811123!amuchb11"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
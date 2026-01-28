Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "amuchb"%string; "789"%string; "10"%string; "78"%string; "newlines"%string; "1long"%string; "13"%string; "14"%string; "15"%string; "16"%string; "lazy"%string; "iif3🧐"%string; "18"%string; "11"%string; "789"%string] ("123amuchb7891078newlines1long13141516lazyiif3🧐1811789"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
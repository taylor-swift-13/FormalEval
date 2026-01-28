Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "456"%string; "7989"%string; "10"%string; "78"%string; "11"%string; "1long"%string; "13"%string; "14"%string; "115"%string; "16"%string; "6"%string; "313"%string; "18"%string; "11"%string; "789"%string; "13"%string; "78"%string; "18"%string] ("12345679891078111long13141151663131811789137818"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
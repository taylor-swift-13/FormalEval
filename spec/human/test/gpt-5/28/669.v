Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["no"%string; "789"%string; "10"%string; "11"%string; "12"%string; "13"%string; "14"%string; "15"%string; "16"%string; "thea"%string; "lazy"%string; "3113"%string; "18"%string] ("no78910111213141516thealazy311318"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
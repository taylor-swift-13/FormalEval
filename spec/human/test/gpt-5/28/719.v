Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "2"%string; "3"%string; ""%string; "456"%string; "66"%string; "8"%string; "11"%string; "9"%string; "10"%string; ""%string] ("12345666811910"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
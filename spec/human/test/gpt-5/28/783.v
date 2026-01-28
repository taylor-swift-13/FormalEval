Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["456"%string; "10"%string; "11"%string; "12"%string; "18characters10"%string; "13"%string; "14"%string; "15"%string; "1"%string; "17"%string; "14"%string] ("45610111218characters1013141511714"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
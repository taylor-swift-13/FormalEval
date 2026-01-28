Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["456"%string; "789"%string; "10"%string; "11"%string; "12"%string; "113"%string; "17"%string; "woodch8789uck"%string; "11"%string; "123!amuchb"%string; "11"%string; "123!amuchb"%string]
  ("45678910111211317woodch8789uck11123!amuchb11123!amuchb"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
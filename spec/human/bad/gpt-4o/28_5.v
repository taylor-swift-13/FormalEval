Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_1 : problem_28_spec ["python"; "is"; "a"; "great"; "language"] "pythonisagreatlanguage".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
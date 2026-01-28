Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_strings :
  problem_28_spec ["python"; "aa"; "is"; "a"; "great"; "language"] "pythonaaisagreatlanguage".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
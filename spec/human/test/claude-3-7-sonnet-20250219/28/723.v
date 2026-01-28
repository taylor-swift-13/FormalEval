Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_concat_numbers_and_emoji :
  problem_28_spec ["123"; "789"; "10"; "11"; "12"; "13"; "🦌🦌"; "16"; "17"; "18"] "12378910111213🦌🦌161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
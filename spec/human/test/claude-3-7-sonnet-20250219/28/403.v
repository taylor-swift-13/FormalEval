Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_emoji_list :
  problem_28_spec ["🦁"; "🦊"; "🐼"; "🐨"; "7🐯"; "🦛"; "🦌"; "multipule"; "🦜"; "🐢"; "$multipule"; "🦉"] "🦁🦊🐼🐨7🐯🦛🦌multipule🦜🐢$multipule🦉".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
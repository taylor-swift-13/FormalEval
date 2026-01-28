Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_bear_lion_fox :
  problem_28_spec ["🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "🦌"; "🦉"; "🦜"; "77🐢"; "abcdefHello, Woworldrld!🌞🐻"; "🐻"; "🐻"] "🐻🦁🦊🐼🐨🐯🦛🦌🦉🦜77🐢abcdefHello, Woworldrld!🌞🐻🐻🐻".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
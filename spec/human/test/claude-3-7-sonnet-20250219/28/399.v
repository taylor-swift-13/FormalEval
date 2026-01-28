Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_long_emoji_and_text :
  problem_28_spec ["🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "hello
w14orld"; "🦛"; "🦌"; ""; "5"; "🐢"; "🦌"] "🐻🦁🦊🐼🐨🐯hello
w14orld🦛🦌5🐢🦌".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.
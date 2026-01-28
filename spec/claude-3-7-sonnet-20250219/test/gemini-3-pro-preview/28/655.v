Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode: concatenate_spec ["🐻"; "🦁"; "🦌🦌"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "🦌"; "🦢"; "9"; "🦉"; "🦜"; "🐢How"; "🦌"] "🐻🦁🦌🦌🦊🐼🐨🐯🦛🦌🦢9🦉🦜🐢How🦌".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
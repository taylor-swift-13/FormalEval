Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode: concatenate_spec ["🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦁any"; "🦛"; "🦌"; "🦢"; "9"; "🦉"; "🐢"; "🦉"] "🐻🦁🦊🐼🐨🐯🦁any🦛🦌🦢9🦉🐢🦉".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
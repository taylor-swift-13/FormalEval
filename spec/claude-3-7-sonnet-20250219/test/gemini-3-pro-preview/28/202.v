Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_symbols: concatenate_spec ["🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "17"; "🦌"; "🦉"; "🦜"; "🐢"; "🐻"] "🐻🦁🦊🐼🐨🐯🦛17🦌🦉🦜🐢🐻".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
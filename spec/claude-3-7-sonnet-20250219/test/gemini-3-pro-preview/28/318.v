Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode: concatenate_spec ["🐻"; "🦁"; "🦊"; "9"; "🐯"; "🦛"; "17"; "🦌"; "🦉"; "🦜"; "🐢"; "🐻"; "🐨"; "🐨"; "🦊"] "🐻🦁🦊9🐯🦛17🦌🦉🦜🐢🐻🐨🐨🦊".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
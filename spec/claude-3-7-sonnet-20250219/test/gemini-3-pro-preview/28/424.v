Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec [
"this
string
has
multiple
newlines🦜🦜"; "🐻"; "🦁"; "🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; "🦉"; "minultiple🦌"; "🦢"; "🦉"; "🦜"; "🐢"; "🦉"]
"this
string
has
multiple
newlines🦜🦜🐻🦁🦊🐼🐨🐯🦛18🦉minultiple🦌🦢🦉🦜🐢🦉".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
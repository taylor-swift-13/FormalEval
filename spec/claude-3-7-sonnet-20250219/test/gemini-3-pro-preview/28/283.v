Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["🐻"; "🦊"; "quick"; "🐼"; "🐯"; "🦛"; "18"; "🦌"; "🦢"; "this
string
has
mulntiple
newlines"; "🦉"; "could🐢"; "!!"; "🐢"; "🦉"] "🐻🦊quick🐼🐯🦛18🦌🦢this
string
has
mulntiple
newlines🦉could🐢!!🐢🦉".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
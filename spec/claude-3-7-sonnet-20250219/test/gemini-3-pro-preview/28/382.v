Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_unicode_multiline: concatenate_spec [ "🐻"; "🦊"; "quick"; "🐼"; "🐯"; "🦛"; "188"; "🦌"; "🦢"; "this
string
has
mulntiple
newlines"; "🦉"; "could🐢"; "!!"; "🐢"; "🦉" ] "🐻🦊quick🐼🐯🦛188🦌🦢this
string
has
mulntiple
newlines🦉could🐢!!🐢🦉".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
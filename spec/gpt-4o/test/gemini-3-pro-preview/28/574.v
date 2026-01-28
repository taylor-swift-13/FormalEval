Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["🐻"; "🦁"; "🦊"; "🐼"; "woodchuck"; "🐨"; "🐯"; "🦛"; "🦌"; "🦢"; "9"; "🦉"; "🦜"; "no
newline
this
is
a..
long
string🐢"; "🦌"; "🦁"; "woodchuck"; "🐨"] "🐻🦁🦊🐼woodchuck🐨🐯🦛🦌🦢9🦉🦜no
newline
this
is
a..
long
string🐢🦌🦁woodchuck🐨".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
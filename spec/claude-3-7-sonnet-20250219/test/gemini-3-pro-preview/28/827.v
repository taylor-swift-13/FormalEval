Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec [
"hello
world"; "this
string
has
multiple
newlines"; "hello
world"; "this
string
has
multiple
newlines"; "this
string
has
multiple
newlines"] "hello
worldthis
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlinesthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
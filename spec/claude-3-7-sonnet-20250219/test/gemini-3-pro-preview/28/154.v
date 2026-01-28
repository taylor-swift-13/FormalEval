Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec ["hello
world"; "jum"; "this
string
has
multiple
newlines"; "jumps"; "jumps"] "hello
worldjumthis
string
has
multiple
newlinesjumpsjumps".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
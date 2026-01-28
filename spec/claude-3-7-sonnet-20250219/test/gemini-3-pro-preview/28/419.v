Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec ["hello
world"; "this
string
has
multiple
newlines"; "chthis
string
has
multiple
newleinesukck"; "this
string
has
multipule
newlines"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world"] "hello
worldthis
string
has
multiple
newlineschthis
string
has
multiple
newleinesukckthis
string
has
multipule
newlineshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
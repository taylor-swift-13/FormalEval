Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec [ "hello
world"; "this
string
has
multiple
newlines"; "1or"; "jumps"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world" ] "hello
worldthis
string
has
multiple
newlines1orjumpshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec [ "hello
world"; "this
string
has
multiple
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hello
world"; "this
string
has
mulntiple
newlines" ] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshello
worldthis
string
has
mulntiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
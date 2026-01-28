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
newlines"; "no"; "hello
world"; "this
string
has
mulntiple
newlines"; "this
string
has
multipule
newlines" ] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlinesnohello
worldthis
string
has
mulntiple
newlinesthis
string
has
multipule
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
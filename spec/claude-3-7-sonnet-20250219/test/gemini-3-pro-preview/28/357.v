Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines: concatenate_spec [ "t!!shis
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "hello
world"; "jumps"; "t!!his
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "jumps"; "hello
world"; "t!!his
string
has
multiple
newlines" ] "t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumpshello
worldt!!his
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
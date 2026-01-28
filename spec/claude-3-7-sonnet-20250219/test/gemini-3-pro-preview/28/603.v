Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec [ "chara1longcters"; "hello
world"; "characters"; "no
newline
this
is
a..
long
string"; "has"; "this
string
has
multiple
newlines" ] "chara1longctershello
worldcharactersno
newline
this
is
a..
long
stringhasthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
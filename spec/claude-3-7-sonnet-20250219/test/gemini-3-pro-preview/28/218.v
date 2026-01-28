Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate: concatenate_spec [ "hello
w555orld"; "this
string
has
multiple
newlines"; "no
newline
this
is

a..
long
string" ] "hello
w555orldthis
string
has
multiple
newlinesno
newline
this
is

a..
long
string".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
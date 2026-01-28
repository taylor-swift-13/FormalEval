Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_newlines : concatenate_spec [ "hello
world"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines" ] "hello
worldthis
string
has
multiple
newlinesno
newline
this
is
a..
long
stringthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.
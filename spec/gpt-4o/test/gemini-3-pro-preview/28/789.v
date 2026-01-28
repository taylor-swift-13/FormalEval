Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1 : concatenate_spec [ "hello
world"; "no
newline
this
is
a..
long
string"; "this
string
has
multiple
newlines"; "hello
world" ] "hello
worldno
newline
this
is
a..
long
stringthis
string
has
multiple
newlineshello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
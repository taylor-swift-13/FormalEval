Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "hello
world"; "newlines"; "no
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
world"; "this
string
has
multiple
newlines" ] "hello
worldnewlinesno
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
worldthis
string
has
multiple
newlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.
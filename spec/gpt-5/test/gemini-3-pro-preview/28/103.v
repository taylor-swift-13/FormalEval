Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "hello
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
string" ] "hello
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
string".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.